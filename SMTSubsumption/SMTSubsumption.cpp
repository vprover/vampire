#include "SMTSubsumption.hpp"
#include "OldSubstitutionTheory.hpp"
#include "SMTSubsumption/minisat/Solver.h"
#include "SMTSubsumption/slice.hpp"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"
#include "Lib/BinaryHeap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLMatcher.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Debug/RuntimeStatistics.hpp"

#include <chrono>
#include <iostream>
#include <iomanip>
#include <new>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

#include "SMTSubsumption/cdebug.hpp"



template <typename T, typename Allocator = STLAllocator<T>>
class pinned_vector
{
  // owns a vector but hides all interfaces that may re-allocate,
  // effectively pinning the pointer v->data() in memory.
  // only constructor: move from existing vector

  pinned_vector(std::vector<T, Allocator>&& v)
    : v{std::move(v)}
  { }

  // TODO

private:
  std::vector<T, Allocator> v;
};


/****************************************************************************
 * Original subsumption implementation (from ForwardSubsumptionAndResolution)
 ****************************************************************************/

namespace OriginalSubsumption {


struct ClauseMatches {
  CLASS_NAME(OriginalSubsumption::ClauseMatches);
  USE_ALLOCATOR(ClauseMatches);

private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  ClauseMatches(const ClauseMatches&);
  ClauseMatches& operator=(const ClauseMatches&);
public:
  ClauseMatches(Clause* cl) : _cl(cl), _zeroCnt(cl->length())
  {
    unsigned clen=_cl->length();
    _matches=static_cast<LiteralList**>(ALLOC_KNOWN(clen*sizeof(void*), "Inferences::ClauseMatches"));
    for(unsigned i=0;i<clen;i++) {
      _matches[i]=0;
    }
  }
  ~ClauseMatches()
  {
    unsigned clen=_cl->length();
    for(unsigned i=0;i<clen;i++) {
      LiteralList::destroy(_matches[i]);
    }
    DEALLOC_KNOWN(_matches, clen*sizeof(void*), "Inferences::ClauseMatches");
  }

  void addMatch(Literal* baseLit, Literal* instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }
  void addMatch(unsigned bpos, Literal* instLit)
  {
    if(!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit,_matches[bpos]);
  }
  void fillInMatches(LiteralMiniIndex* miniIndex)
  {
    unsigned blen=_cl->length();

    for(unsigned bi=0;bi<blen;bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while(instIt.hasNext()) {
	Literal* matched=instIt.next();
	addMatch(bi, matched);
      }
    }
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause* _cl;
  unsigned _zeroCnt;
  LiteralList** _matches;

  class ZeroMatchLiteralIterator
  {
  public:
    ZeroMatchLiteralIterator(ClauseMatches* cm)
    : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if(!cm->_zeroCnt) {
	_remaining=0;
      }
    }
    bool hasNext()
    {
      while(_remaining>0 && *_mlists) {
	_lits++; _mlists++; _remaining--;
      }
      return _remaining;
    }
    Literal* next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }
  private:
    Literal** _lits;
    LiteralList** _mlists;
    unsigned _remaining;
  };
};



bool checkForSubsumptionResolution(Clause* cl, ClauseMatches* cms, Literal* resLit)
{
  Clause* mcl = cms->_cl;
  unsigned mclen = mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if (zmli.hasNext()) {
    while (zmli.hasNext()) {
      Literal* bl = zmli.next();
      if (!MatchingUtils::match(bl, resLit, true)) {
        return false;
      }
    }
  }
  else {
    bool anyResolvable = false;
    for (unsigned i = 0; i < mclen; i++) {
      if (MatchingUtils::match((*mcl)[i], resLit, true)) {
        anyResolvable = true;
        break;
      }
    }
    if (!anyResolvable) {
      return false;
    }
  }

  return MLMatcher::canBeMatched(mcl, cl, cms->_matches, resLit);
}



class OriginalSubsumptionImpl
{
  private:
    Kernel::MLMatcher matcher;
    ClauseMatches* cms = nullptr;
  public:

    void printStats(std::ostream& out)
    {
      out << "Stats: " << matcher.getStats() << std::endl;
    }

    bool setup(Clause* side_premise, Clause* main_premise)
    {
      Clause* mcl = side_premise;
      Clause* cl = main_premise;
      LiteralMiniIndex miniIndex(cl);  // TODO: to benchmark forward subsumption, we might want to move this to the benchmark setup instead? as the work may be shared between differed side premises.

      unsigned mlen = mcl->length();

      if (cms) { delete cms; cms = nullptr; }
      ASS(cms == nullptr);
      cms = new ClauseMatches(mcl);  // NOTE: why "new"? because the original code does it like this as well.
      cms->fillInMatches(&miniIndex);

      if (cms->anyNonMatched()) {
        delete cms;
        cms = nullptr;
        return false;
      }

      matcher.init(mcl, cl, cms->_matches, true);
      return true;
    }

    bool solve()
    {
      ASS(cms);
      bool isSubsumed = matcher.nextMatch();
      delete cms;
      cms = nullptr;
      return isSubsumed;
    }

    bool checkSubsumption(Kernel::Clause* side_premise, Kernel::Clause* main_premise)
    {
      return setup(side_premise, main_premise) && solve();
    }
};
using Impl = OriginalSubsumptionImpl;  // shorthand if we use qualified namespace


}  // namespace OriginalSubsumption

/****************************************************************************/
/****************************************************************************/
/****************************************************************************/















/****************************************************************************
 * SMT-Subsumption for benchmark
 ****************************************************************************/


// TODO: early exit in case time limit hits, like in MLMatcher which checks every 50k iterations if time limit has been exceeded


// Binder that stores mapping into an array, using linear search to check entries.
// Rationale: due to CPU caches, this is faster than maps for a small number of bindings.
//            Typically, literals have few variables.
class VectorStoringBinder
{
  CLASS_NAME(VectorStoringBinder);
  USE_ALLOCATOR(VectorStoringBinder);

public:
  using Var = unsigned int;
  using Entry = std::pair<Var, TermList>;
  using Vector = vvector<Entry>;

  VectorStoringBinder(Vector& bindings_storage)
    : m_bindings_storage{bindings_storage}
    , m_bindings_start{bindings_storage.size()}
  { }

  VectorStoringBinder(VectorStoringBinder&) = delete;
  VectorStoringBinder& operator=(VectorStoringBinder&) = delete;
  VectorStoringBinder(VectorStoringBinder&&) = delete;
  VectorStoringBinder& operator=(VectorStoringBinder&&) = delete;

  bool bind(Var var, TermList term)
  {
    for (auto it = m_bindings_storage.begin() + m_bindings_start; it != m_bindings_storage.end(); ++it) {
      Entry entry = *it;
      if (entry.first == var)
      {
        // 'var' is already bound => successful iff we bind to the same term again
        return entry.second == term;
      }
    }
    // 'var' is not bound yet => store new binding
    m_bindings_storage.emplace_back(var, term);
    return true;
  }

  void specVar(unsigned var, TermList term)
  {
    ASSERTION_VIOLATION;
  }

  void reset()
  {
    ASS_GE(m_bindings_storage.size(), m_bindings_start);
    m_bindings_storage.resize(m_bindings_start);
  }

  size_t index() const
  {
    return m_bindings_start;
  }

  size_t size() const
  {
    ASS_GE(m_bindings_storage.size(), m_bindings_start);
    return m_bindings_storage.size() - m_bindings_start;
  }

private:
  Vector& m_bindings_storage;
  /// First index of the current bindings in m_bindings_storage
  size_t const m_bindings_start;
};


/*
template <typename T>
class SectionedVector
{
  CLASS_NAME(SectionedVector);
  USE_ALLOCATOR(SectionedVector);

  struct SectionToken {
    size_t index;
  };
  SectionToken begin_section();
  end_section(SectionToken t);

private:
  using index_type = uint32_t;  // should technically be size_t but for our small stuff 32 bits are more than enough
  struct SectionRef {
    index_type index;
    index_type size;
  };
  vvector<SectionRef> m_sections;
  vvector<T> m_storage;
};
*/



// Optimizations log:
// - move MapBinder declaration in setup() out of loop: ~5000ns
// - allocate all variables at once: ~2000ns
// - remove clause deletion from solver: imperceptible (but note that this is only setup)
// - use DHMap instead of std::unordered_map: ~5000ns
// (benchmark smt_setup_1 of file slog_GEO312+1_manydecisions.txt)


/// Possible match alternative for a certain literal of the side premise.
struct Alt
{
  // Literal* lit;  // the FOL literal
  // unsigned j;    // index of lit in the main_premise
  Minisat::Var b;  // the b_{ij} representing this choice in the SAT solver
  // bool reversed;
};


class SMTSubsumptionImpl
{
  private:
    Minisat::Solver solver;

  public:

    struct BindingsRef {
      uint32_t index;
      uint32_t size;
      BindingsRef(VectorStoringBinder const& binder)
        : index(binder.index())
        , size(binder.size())
      { }
      /// last index + 1
      uint32_t end() {
        return index + size;
      }
    };

    /// Set up the subsumption problem.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setup2(Kernel::Clause* side_premise, Kernel::Clause* main_premise)
    {
      CDEBUG("SMTSubsumptionImpl::setup2()");

      // TODO: use miniindex
      // LiteralMiniIndex const main_premise_mini_index(main_premise);
      // (need to extend InstanceIterator to a version that returns the binder)
      // then in loop: LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);

      // Pre-matching
      // Determine which literals of the side_premise can be matched to which
      // literals of the main_premise when considered on their own.
      // Along with this, we create variables b_ij and the mapping for substitution
      // constraints.
      // vvector<vvector<Alt>> alts;
      // alts.reserve(side_premise->length());

      // TODO: preserve alignment for storage? to 8-byte boundary (i.e., lowest 3 bits of pointers should be 0, exactly as if Clause* was allocated normally)

      // The match clauses + AtMostOne constraints saying that each base literal is matches to exactly one instance literal.
      // Worst case: each base literal may be matchable to two boolean vars per instance literal (two orientations of equalities).
      // First slot stores the length.
      size_t clause_maxsize = 1 + 2 * main_premise->length();
      size_t clause_storage_size = side_premise->length() * clause_maxsize;
      vvector<uint32_t> clause_storage;
      clause_storage.reserve(clause_storage_size);
      // clause_storage.ensure(clause_storage_size);
      // NOTE: match clauses+constraints can be packed densely.

/*
      // for each instance literal (of main_premise),
      // the possible variables indicating a match with the instance literal
      vvector<vvector<Minisat::Var>> possible_base_vars;
      // start with empty vector for each instance literal
      possible_base_vars.resize(main_premise->length());
      */

      // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
      // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
      // First slot stores the length.
      size_t max_instance_constraint_len = 1 + 2 * side_premise->length();
      size_t instance_constraints_storage_size = main_premise->length() * max_instance_constraint_len;
      // vvector<uint32_t> instance_constraints_storage;
      // instance_constraints_storage.resize( main_premise->length() * (1 + max_instance_constraint_len) );
      DArray<uint32_t> instance_constraints_storage;
      instance_constraints_storage.ensure(instance_constraints_storage_size);  // TODO: if VDEBUG, set all entries to 999999 or smth like that
      // uint32_t* instance_constraints_storage = static_cast<uint32_t*>(ALLOC_UNKNOWN(instance_constraints_storage_size * sizeof(uint32_t), "hoho"));  // somehow even this initializes the memory? so whatever...
      // initialize sizes to 0
      for (size_t i = 0; i < instance_constraints_storage.size(); i += max_instance_constraint_len) {
        instance_constraints_storage[i] = 0;
      }
      // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.

      // Minisat::Var b ... boolean variable with FO bindings attached
      // bindings_table[b] ... index/size of FO bindings for b
      // bindings_storage[bindings_table[b].index .. bindings_table[b].end] ... FO bindings for b
      vvector<BindingsRef> bindings_table;
      bindings_table.reserve(32);
      vvector<std::pair<unsigned, TermList>> bindings_storage;
      bindings_storage.reserve(128);

      // Matching for subsumption checks whether
      //
      //      side_premise\theta \subseteq main_premise
      //
      // holds.
      Minisat::Var nextVar = 0;
      for (unsigned i = 0; i < side_premise->length(); ++i) {
        Literal* base_lit = side_premise->literals()[i];

        size_t clause_index = clause_storage.size();
        clause_storage.push_back(0);  // size field
        // vvector<Alt> base_lit_alts;

        for (unsigned j = 0; j < main_premise->length(); ++j) {
          Literal* inst_lit = main_premise->literals()[j];

          if (!Literal::headersMatch(base_lit, inst_lit, false)) {
            continue;
          }

          {
            VectorStoringBinder binder(bindings_storage);
            if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
              Minisat::Var b = nextVar++;

              if (binder.size() > 0) {
                ASS(!base_lit->ground());
              }
              else {
                ASS(base_lit->ground());
                ASS_EQ(base_lit, inst_lit);
                // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
                // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
              }

              ASS_EQ(bindings_table.size(), b);
              bindings_table.emplace_back(binder);

              // base_lit_alts.push_back({ .b = b, });
              clause_storage.push_back(Minisat::index(Minisat::Lit(b)));
              uint32_t* inst_constraint = &instance_constraints_storage[j * max_instance_constraint_len];
              inst_constraint[0] += 1;
              inst_constraint[inst_constraint[0]] = Minisat::index(Minisat::Lit(b));
              // possible_base_vars[j].push_back(b);
            } else {
              binder.reset();
            }
          }

          if (base_lit->commutative()) {
            ASS_EQ(base_lit->arity(), 2);
            ASS_EQ(inst_lit->arity(), 2);
            VectorStoringBinder binder(bindings_storage);
            if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {

              Minisat::Var b = nextVar++;

              ASS_EQ(bindings_table.size(), b);
              bindings_table.emplace_back(binder);

              // base_lit_alts.push_back({ .b = b, });
              clause_storage.push_back(Minisat::index(Minisat::Lit(b)));
              uint32_t* inst_constraint = &instance_constraints_storage[j * max_instance_constraint_len];
              inst_constraint[0] += 1;
              inst_constraint[inst_constraint[0]] = Minisat::index(Minisat::Lit(b));
              // possible_base_vars[j].push_back(b);
            } else {
              binder.reset();
            }
          }
        }
        uint32_t clause_size = clause_storage.size() - clause_index - 1;
        if (clause_size == 0) {
          // no matches for this base literal => conflict on root level due to empty clause
          return false;
        }
        clause_storage[clause_index] = clause_size;
        // if (base_lit_alts.empty()) {
        //   return false;
        // }
        // alts.push_back(std::move(base_lit_alts));
      }

      solver.newVars(nextVar);

      CDEBUG("setting substitution theory...");
      // solver.setSubstitutionTheory(std::move(stc));  // TODO lazy version

      // // Pre-matching done
      // for (auto const& v : alts) {
      //   if (v.empty()) {
      //     ASSERTION_VIOLATION; // should have been discovered above
      //     // There is a base literal without any possible matches => abort
      //     return false;
      //   }
      // }
      // return bindings_storage.size() > 10 && bindings_storage.back().first > 5
      //       && instance_constraints_storage.size() > 20 && instance_constraints_storage[20] > 3
      //       && clause_storage.size() > 5 && clause_storage[5] > 1;

      using Minisat::Lit;

      std::cerr << "clause_storage:";
      for (auto x : clause_storage) {
        std::cerr << " " << x;
      }
      std::cerr << std::endl;

      { // add match clauses/constraints
      size_t c_index = 0;
      while (c_index < clause_storage.size()) {
        std::cerr << "Adding clause at index " << c_index << std::endl;
        uint32_t* c_size = &clause_storage[c_index];
        uint32_t* c_lits = &clause_storage[c_index + 1];
        uint32_t const c_original_size = *c_size;
        ASS_G(c_original_size, 0);  // otherwise we would have returned in the matching loop already

        std::cerr << "  *c_size = " << *c_size << std::endl;
        std::cerr << "  c_original_size = " << c_original_size << std::endl;
        for (int k = 0; k < c_original_size; ++k) {
          std::cerr << "  c_lits[" << k << "] = " << c_lits[k] << std::endl;
        }

        // Clean the constraint (remove literals with already-known value)
        // TODO: maybe extract this into a separate function?
        int n_true = 0;
        int i = 0, j = 0;
        while (j < *c_size) {
          Lit l = Minisat::toLit(c_lits[j]);
          Minisat::lbool lvalue = solver.value(l);
          if (lvalue == Minisat::l_True) {
            n_true += 1;
            // skip literal (in this case we don't really care about the constraint anymore)
            std::cerr << "    skip " << j << std::endl;
            ++j;
          }
          else if (lvalue == Minisat::l_False) {
            // skip literal
            std::cerr << "    skip " << j << std::endl;
            ++j;
          }
          else {
            ASS_EQ(lvalue, Minisat::l_Undef);
            // copy literal
            std::cerr << "    copy " << j << " to " << i << std::endl;
            c_lits[i] = c_lits[j];
            ++i; ++j;
          }
        }
        *c_size = i;

        std::cerr << "  *c_size = " << *c_size << std::endl;
        std::cerr << "  c_original_size = " << c_original_size << std::endl;
        for (int k = 0; k < c_original_size; ++k) {
          std::cerr << "  c_lits[" << k << "] = " << c_lits[k] << std::endl;
        }

        // we use the same storage for both Clause and AtMostOne constraint
        Minisat::Clause* c1 = reinterpret_cast<Minisat::Clause*>(&clause_storage[c_index]);   // use std::launder? see https://stackoverflow.com/a/39382728 (but requires C++17)
        Minisat::AtMostOne* c2 = reinterpret_cast<Minisat::AtMostOne*>(&clause_storage[c_index]);   // use std::launder?
        // ASS(!c1->learnt());
        ASS_EQ(*c_size, c1->size());  // TODO: if VDEBUG check contents too?
        ASS_EQ(*c_size, c2->size());  // TODO: if VDEBUG check contents too?

        if (n_true == 0) {
          // At least one must be true
          solver.addClause_unchecked(c1);
          // At most one must be true
          if (c2->size() >= 2) {
            solver.addConstraint_AtMostOne_unchecked(c2);
          }
        } else if (n_true == 1) {
          // one is already true => skip clause, propagate AtMostOne constraint
          for (int k = 0; k < c2->size(); ++k) {
            Lit l = (*c2)[k];
            ASS(solver.value(l) == Minisat::l_Undef);
            solver.addUnit(~l);
          }
        } else {
          ASS(n_true >= 2);
          // conflict at root level due to AtMostOne constraint
          return false;
        }

        // go to next clause
        c_index += 1 + c_original_size;
      }
      ASS_EQ(c_index, clause_storage.size());
      }
/* OLD below
      // Add constraints:
      // \Land_i ExactlyOneOf(b_{i1}, ..., b_{ij})
      Minisat::vec<Lit> ls;
      for (auto const& v : alts) {
        ls.clear();
        // Collect still-undefined literals
        int n_true = 0;
        for (auto const& alt : v) {
          Lit l = Lit(alt.b);
          Minisat::lbool lvalue = solver.value(l);
          if (lvalue == Minisat::l_True) {
            // skip clause and AtMostOne-constraint
            n_true += 1;
          } else if (lvalue == Minisat::l_False) {
            // skip literal
          } else {
            ASS_EQ(lvalue, Minisat::l_Undef);
            ls.push(l);
          }
        }
        if (n_true == 0) {
          // At least one must be true
          solver.addClause_unchecked(ls);
          // At most one must be true
          if (ls.size() >= 2) {
            solver.addConstraint_AtMostOne_unchecked(ls);
          }
        } else if (n_true == 1) {
          // one is already true => skip clause, propagate AtMostOne constraint
          for (auto const& alt : v) {
            Lit l = Lit(alt.b);
            if (solver.value(l) == Minisat::l_Undef) {
              solver.addUnit(~l);
            }
          }
        } else {
          ASS(n_true >= 2);
          // conflict at root level due to AtMostOne constraint
          return false;
        }
      }
      */

      // Add constraints:
      // \Land_j AtMostOneOf(b_{1j}, ..., b_{ij})
      for (size_t c_index = 0; c_index < instance_constraints_storage.size(); c_index += max_instance_constraint_len) {
        uint32_t* c_size = &instance_constraints_storage[c_index];  // TODO
        uint32_t* c_lits = &instance_constraints_storage[c_index + 1];

        // Clean the constraint (remove literals with already-known value)
        // => actually, this should be done in the solver in addConstraint_AtMostOne_unchecked(AtMostOne*)
        //    (the 'unchecked' then just is about the properties no-duplicates and sorted.)
        // => OTOH, above we can use the same structure for clause AND constraint. So we don't really want to do this twice. (or modify at all, after adding one)
        int n_true = 0;
        int i = 0, j = 0;
        while (j < *c_size) {
          Lit l = Minisat::toLit(c_lits[j]);
          Minisat::lbool lvalue = solver.value(l);
          if (lvalue == Minisat::l_True) {
            n_true += 1;
            // skip literal (in this case we don't really care about the constraint anymore)
            ++j;
          }
          else if (lvalue == Minisat::l_False) {
            // skip literal
            ++j;
          }
          else {
            ASS_EQ(lvalue, Minisat::l_Undef);
            // copy literal
            c_lits[i] = c_lits[j];
            ++i; ++j;
          }
        }
        *c_size = i;
        Minisat::AtMostOne* c = reinterpret_cast<Minisat::AtMostOne*>(&instance_constraints_storage[c_index]);
        ASS_EQ(*c_size, c->size());  // TODO if VDEBUG check contents too?

        if (n_true == 0) {
          // At most one must be true
          if (c->size() >= 2) {
            solver.addConstraint_AtMostOne_unchecked(c);
          }
        }
        else if (n_true == 1) {
          // one is already true => propagate AtMostOne constraint
          for (int k = 0; k < c->size(); ++k) {
            Lit l = (*c)[k];
            ASS(solver.value(l) == Minisat::l_Undef);
            solver.addUnit(~l);
          }
        }
        else {
          ASS(n_true >= 2);
          // conflict at root level due to AtMostOne constraint
          return false;
        }

      /* OLD below
        if (w.size() >= 2) {
          ls.clear();
          int n_true = 0;
          for (auto const b : w) {
            Lit l = Lit(b);
            Minisat::lbool lvalue = solver.value(l);
            if (lvalue == Minisat::l_True) {
              n_true += 1;
            }
            else if (lvalue == Minisat::l_False) {
              // skip literal
            }
            else {
              ASS_EQ(lvalue, Minisat::l_Undef);
              ls.push(l);
            }
            // ls.push(Lit(b));
          }
          // solver.addConstraint_AtMostOne(ls);
          if (n_true == 0) {
            // At most one must be true
            if (ls.size() >= 2) {
              solver.addConstraint_AtMostOne_unchecked(ls);
            }
          }
          else if (n_true == 1) {
            // one is already true => propagate AtMostOne constraint
            for (auto const b : w) {
              Lit l = Lit(b);
              if (solver.value(l) == Minisat::l_Undef) {
                solver.addUnit(~l);
              }
            }
          }
          else {
            ASS(n_true >= 2);
            // conflict at root level due to AtMostOne constraint
            return false;
          }
        }
        */
      }

      return true;
    }



    void printStats(std::ostream& out)
    {
      // printf("==================================[MINISAT]===================================\n");
      // printf("| Conflicts |     ORIGINAL     |              LEARNT              | Progress |\n");
      // printf("|           | Clauses Literals |   Limit Clauses Literals  Lit/Cl |          |\n");
      // printf("==============================================================================\n");
      // printf("| %9d | %7d %8d | %7d %7d %8d %7.1f | %6.3f %% |\n",
      //        (int)solver.stats.conflicts,
      //        solver.nClauses(), (int)solver.stats.clauses_literals,
      //        -1, solver.nLearnts(), (int)solver.stats.learnts_literals, (double)solver.stats.learnts_literals / solver.nLearnts(),
      //        -1);
      // fflush(stdout);
      out << "Starts:       " << std::setw(8) << solver.stats.starts << std::endl;
      out << "Decisions:    " << std::setw(8) << solver.stats.decisions << std::endl;
      out << "Propagations: " << std::setw(8) << solver.stats.propagations << std::endl;
      out << "Conflicts:    " << std::setw(8) << solver.stats.conflicts << std::endl;
      out << "Learned:      " << std::setw(8) << solver.nLearnts() << " clauses, " << solver.stats.learnts_literals << " literals" << std::endl;
      out << "Minimized:    " << std::setw(8) << (solver.stats.max_literals - solver.stats.tot_literals) << " literals" << std::endl;
      out << "Clause db:    " << std::setw(8) << solver.stats.db_reductions << " reductions, " << solver.stats.db_simplifications << " simplifications" << std::endl;
    }

    /// Set up the subsumption problem.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setup(Kernel::Clause* side_premise, Kernel::Clause* main_premise, Minisat::VarOrderStrategy vo_strategy = Minisat::VarOrderStrategy::MinisatDefault)
    {
      CDEBUG("SMTSubsumptionImpl::setup()");
      // solver.reset();  // TODO
#if VDEBUG
      solver.verbosity = 1;
#endif

      // TODO: use miniindex
      // LiteralMiniIndex const main_premise_mini_index(main_premise);

      // Pre-matching
      // Determine which literals of the side_premise can be matched to which
      // literals of the main_premise when considered on their own.
      // Along with this, we create variables b_ij and the mapping for substitution
      // constraints.
      vvector<vvector<Alt>> alts;
      alts.reserve(side_premise->length());

      // for each instance literal (of main_premise),
      // the possible variables indicating a match with the instance literal
      vvector<vvector<Minisat::Var>> possible_base_vars;
      // start with empty vector for each instance literal
      possible_base_vars.resize(main_premise->length());

      SubstitutionTheoryConfiguration stc;
      MapBinder binder;

      Minisat::VarOrder_info& vo_info = solver.vo_info;
      vo_info.strategy = vo_strategy;
      vo_info.var_baselit.clear();
      vo_info.num_baselits = side_premise->length();

      // Matching for subsumption checks whether
      //
      //      side_premise\theta \subseteq main_premise
      //
      // holds.
      Minisat::Var nextVar = 0;
      for (unsigned i = 0; i < side_premise->length(); ++i) {
        Literal* base_lit = side_premise->literals()[i];
        vo_info.baselit_distinctVars.push(base_lit->getDistinctVars());

        vvector<Alt> base_lit_alts;

        // TODO: use LiteralMiniIndex here? (need to extend InstanceIterator to a version that returns the binder)
        // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
        for (unsigned j = 0; j < main_premise->length(); ++j) {
          Literal* inst_lit = main_premise->literals()[j];

          if (!Literal::headersMatch(base_lit, inst_lit, false)) {
            continue;
          }

          binder.reset();
          if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
            Minisat::Var b = nextVar++;
            vo_info.var_baselit.push(i);
            // std::cerr << "Match: " << b << " = " << base_lit->toString() << " -> " << inst_lit->toString() << std::endl;

            if (binder.bindings().size() > 0) {
              ASS(!base_lit->ground());
              auto atom = SubstitutionAtom::from_binder(binder);
              stc.register_atom(b, std::move(atom));
            }
            else {
              ASS(base_lit->ground());
              ASS_EQ(base_lit, inst_lit);
              // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
              // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
              //
              // For now, just register an empty substitution atom.
              auto atom = SubstitutionAtom::from_binder(binder);
              stc.register_atom(b, std::move(atom));
            }

            base_lit_alts.push_back({
                // .lit = inst_lit,
                // .j = j,
                .b = b,
                // .reversed = false,
            });
            possible_base_vars[j].push_back(b);
          }

          if (base_lit->commutative()) {
            ASS_EQ(base_lit->arity(), 2);
            ASS_EQ(inst_lit->arity(), 2);
            binder.reset();
            if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
              auto atom = SubstitutionAtom::from_binder(binder);

              Minisat::Var b = nextVar++;
              vo_info.var_baselit.push(i);
              stc.register_atom(b, std::move(atom));

              base_lit_alts.push_back({
                  // .lit = inst_lit,
                  // .j = j,
                  .b = b,
                  // .reversed = true,
              });
              possible_base_vars[j].push_back(b);
            }
          }
        }
        if (base_lit_alts.empty()) {
          return false;
        }
        alts.push_back(std::move(base_lit_alts));
      }

      solver.newVars(nextVar);
      ASS_EQ(vo_info.var_baselit.size(), solver.nVars());
      ASS_EQ(vo_info.baselit_distinctVars.size(), side_premise->length());

      CDEBUG("setting substitution theory...");
      solver.setSubstitutionTheory(std::move(stc));

      // Pre-matching done
      for (auto const& v : alts) {
        if (v.empty()) {
          ASSERTION_VIOLATION; // should have been discovered above
          // There is a base literal without any possible matches => abort
          return false;
        }
      }

      // Add constraints:
      // \Land_i ExactlyOneOf(b_{i1}, ..., b_{ij})
      using Minisat::Lit;
      Minisat::vec<Lit> ls;
      for (auto const& v : alts) {
        ls.clear();
        // Collect still-undefined literals
        int n_true = 0;
        for (auto const& alt : v) {
          Lit l = Lit(alt.b);
          Minisat::lbool lvalue = solver.value(l);
          if (lvalue == Minisat::l_True) {
            // skip clause and AtMostOne-constraint
            n_true += 1;
          } else if (lvalue == Minisat::l_False) {
            // skip literal
          } else {
            ASS_EQ(lvalue, Minisat::l_Undef);
            ls.push(l);
          }
        }
        if (n_true == 0) {
          // At least one must be true
          solver.addClause_unchecked(ls);
          // At most one must be true
          // NOTE: according to Armin, these redundant constraints may actually be harmful (correspond to blocked clauses which an advanced SAT solver would even remove in preprocessing)
          //       preliminary tests show no difference in #decisions with/without this constraint (so it's better to not add them)
          // if (ls.size() >= 2) {
          //   solver.addConstraint_AtMostOne_unchecked(ls);
          // }
        } else if (n_true == 1) {
          // // one is already true => skip clause, propagate AtMostOne constraint
          // for (auto const& alt : v) {
          //   Lit l = Lit(alt.b);
          //   if (solver.value(l) == Minisat::l_Undef) {
          //     solver.addUnit(~l);
          //   }
          // }
        } else {
          ASS(n_true >= 2);
          // // conflict at root level due to AtMostOne constraint
          // return false;
        }
      }

      // Add constraints:
      // \Land_j AtMostOneOf(b_{1j}, ..., b_{ij})
      for (auto const& w : possible_base_vars) {
        if (w.size() >= 2) {
          ls.clear();
          int n_true = 0;
          for (auto const b : w) {
            Lit l = Lit(b);
            Minisat::lbool lvalue = solver.value(l);
            if (lvalue == Minisat::l_True) {
              n_true += 1;
            }
            else if (lvalue == Minisat::l_False) {
              // skip literal
            }
            else {
              ASS_EQ(lvalue, Minisat::l_Undef);
              ls.push(l);
            }
            // ls.push(Lit(b));
          }
          // solver.addConstraint_AtMostOne(ls);
          if (n_true == 0) {
            // At most one must be true
            if (ls.size() >= 2) {
              solver.addConstraint_AtMostOne_unchecked(ls);
            }
          }
          else if (n_true == 1) {
            // one is already true => propagate AtMostOne constraint
            for (auto const b : w) {
              Lit l = Lit(b);
              if (solver.value(l) == Minisat::l_Undef) {
                solver.addUnit(~l);
              }
            }
          }
          else {
            ASS(n_true >= 2);
            // conflict at root level due to AtMostOne constraint
            return false;
          }
        }
      }

      return true;
    }


    /// Solve the subsumption instance created by the previous call to setup()
    bool solve()
    {
      CDEBUG("SMTSubsumptionImpl::solve()");
      return solver.solve({});
    }

    bool checkSubsumption(Kernel::Clause* side_premise, Kernel::Clause* main_premise)
    {
      return setup(side_premise, main_premise) && solve();
    }
};  // class SMTSubsumptionImpl


/****************************************************************************/
/****************************************************************************/
/****************************************************************************/















/****************************************************************************
 * SMT-Subsumption with custom SAT solver
 ****************************************************************************/


// TODO: early exit in case time limit hits, like in MLMatcher which checks every 50k iterations if time limit has been exceeded
#include "./subsat/subsat.hpp"

// The ground literal prefilter seems to slow us down slightly in general.
// Maybe it's more helpful with induction enabled? since that adds a lot of ground clauses.
#define GROUND_LITERAL_PREFILTER 0


class SMTSubsumption::SMTSubsumptionImpl2
{
  private:

#if 1
    template <typename T>
    using allocator_type = STLAllocator<T>;
#else
    template <typename T>
    using allocator_type = std::allocator<T>;
#endif

    subsat::Solver<allocator_type> solver;

#if GROUND_LITERAL_PREFILTER
    vvector<std::uint8_t> base_used;
    vvector<std::uint8_t> inst_used;
#endif

    Kernel::Clause* m_base = nullptr;
    Kernel::Clause* m_instance = nullptr;

    /// AtMostOne constraints stating that each instance literal may be matched at most once.
    vvector<subsat::AllocatedConstraintHandle> instance_constraints;

    /// Possibly resolved literals for subsumption resolution
    /// Entry: pair of boolean variable and index of the corresponding instance literal.
    vvector<std::pair<subsat::Var, std::uint32_t>> complementary_matches;

  public:
    CLASS_NAME(SMTSubsumptionImpl2);
    USE_ALLOCATOR(SMTSubsumptionImpl2);

    SMTSubsumptionImpl2()
    {
      solver.reserve_variables(64);
      solver.reserve_clause_storage(512);
      solver.theory().reserve(64, 2, 16);
      instance_constraints.reserve(16);
    }

    /// Set up the subsumption problem.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumption(Kernel::Clause* base, Kernel::Clause* instance)
    {
      CALL("SMTSubsumptionImpl2::setupSubsumption");
      solver.clear();
      ASS(solver.empty());
      auto& theory = solver.theory();
      ASS(theory.empty());

      m_base = base;
      m_instance = instance;

#if GROUND_LITERAL_PREFILTER
      base_used.clear();
      ASS(base_used.empty());
      inst_used.clear();
      ASS(inst_used.empty());

      inst_used.resize(instance->length(), false);

      uint32_t base_ground = 0;
      for (unsigned i = 0; i < base->length(); ++i) {
        Literal* base_lit = base->literals()[i];
        if (base_lit->ground()) {
          // Find matching ground literal
          for (unsigned j = 0; j < instance->length(); ++j) {
            Literal* inst_lit = instance->literals()[j];
            if (!inst_used[j] && base_lit == inst_lit) {
              base_used.push_back(true);
              inst_used[j] = true;
              break;
            }
          }
          // No matching ground literal => cannot be subsumed
          if (!base_used[i]) {
            return false;
          }
          base_ground += 1;
        } else {
          base_used.push_back(false);
        }
      }

      uint32_t const remaining_base_len = base->length() - base_ground;
#else
      uint32_t const remaining_base_len = base->length();
#endif

/*
      uint32_t base_n_commutative = 0;
      for (unsigned i = 0; i < base->length(); ++i) {
        Literal* base_lit = base->literals()[i];
        if (base_lit->commutative()) {
          base_n_commutative += 1;
        }
      }
*/

      // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
      // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
      // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
      uint32_t const instance_constraint_maxsize = 2 * remaining_base_len;
      instance_constraints.clear();
      ASS(instance_constraints.empty());
      for (size_t i = 0; i < instance->length(); ++i) {
        instance_constraints.push_back(solver.alloc_constraint(instance_constraint_maxsize));
      }

      // Matching for subsumption checks whether
      //
      //      side_premise\theta \subseteq main_premise
      //
      // holds.
      for (unsigned i = 0; i < base->length(); ++i) {
        Literal* base_lit = base->literals()[i];
        uint32_t match_count = 0;

#if GROUND_LITERAL_PREFILTER
        if (base_used[i]) {
          continue;
        }
#endif

        // Build clause stating that base_lit must be matched to at least one corresponding instance literal.
        // NOTE: we do not need an AtMostOne constraint with the same literals, because
        //       1) different literals will induce different substitutions so this is already built-in via the theory propagation (and because we don't have clauses with duplicate literals)
        //       2) even if 1) were false, a solution with multiple matches could always be reduced to a solution with one match per literal.
        solver.constraint_start();

        for (unsigned j = 0; j < instance->length(); ++j) {
          Literal* inst_lit = instance->literals()[j];

#if GROUND_LITERAL_PREFILTER
          if (inst_used[j]) {
            continue;
          }
#endif
          if (!Literal::headersMatch(base_lit, inst_lit, false)) {
            continue;
          }

          {
            auto binder = theory.start_binder();
            if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
              subsat::Var b = solver.new_variable(i);
              // std::cerr << "Match: " << b << " => " << base_lit->toString() << " -> " << inst_lit->toString() << std::endl;

#if GROUND_LITERAL_PREFILTER
              ASS(!base_lit->ground());
#endif
              if (binder.size() > 0) {
                ASS(!base_lit->ground());
              } else {
                ASS(base_lit->ground());
                ASS_EQ(base_lit, inst_lit);
                // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
                // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
              }

              theory.commit_bindings(binder, b);

              solver.constraint_push_literal(b);
              solver.handle_push_literal(instance_constraints[j], b);
              match_count += 1;
            }
          }

          if (base_lit->commutative()) {
            ASS_EQ(base_lit->arity(), 2);
            ASS_EQ(inst_lit->arity(), 2);
            auto binder = theory.start_binder();
            if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
              subsat::Var b = solver.new_variable(i);

              if (binder.size() > 0) {
                ASS(!base_lit->ground());
              } else {
                ASS(base_lit->ground());
                ASS_EQ(base_lit, inst_lit);
                // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
                // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
              }

              theory.commit_bindings(binder, b);

              solver.constraint_push_literal(b);
              solver.handle_push_literal(instance_constraints[j], b);
              match_count += 1;
            }
          }
        }
        auto handle = solver.constraint_end();
        solver.add_clause_unsafe(handle);

        // If there are no matches for this base literal, we have just added an empty clause.
        // => conflict on root level due to empty clause, abort early
        // if (match_count == 0) { ASS(solver.inconsistent()); }
        // if (solver.inconsistent()) {
        //   return false;
        // }
        if (match_count == 0) {
          return false;
        }
      }

      for (auto& handle : instance_constraints) {
        auto built = solver.handle_build(handle);
        solver.add_atmostone_constraint_unsafe(built);
      }

      return !solver.inconsistent();
    }  // setupSubsumption


    // TODO: allocate this into one big array...
    vvector<vvector<subsat::Var>> inst_normal_matches;
    vvector<vvector<subsat::Var>> inst_compl_matches;
    vvector<subsat::Var> inst_is_compl_matched;

    /// Set up the subsumption resolution problem from scratch.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance)
    {
      CALL("SMTSubsumptionImpl2::setupSubsumptionResolution");
      solver.clear();
      ASS(solver.empty());
      auto& theory = solver.theory();
      ASS(theory.empty());
      complementary_matches.clear();
      ASS(complementary_matches.empty());

      // TODO: improve allocation behaviour
      inst_normal_matches.clear();
      inst_normal_matches.resize(instance->length());
      inst_compl_matches.clear();
      inst_compl_matches.resize(instance->length());
      inst_is_compl_matched.clear();
      inst_is_compl_matched.reserve(instance->length());

      m_base = base;
      m_instance = instance;

      for (unsigned i = 0; i < base->length(); ++i) {
        Literal* const base_lit = base->literals()[i];
        uint32_t match_count = 0;

        // Build clause stating that base_lit must be matched to at least one corresponding instance literal.
        solver.constraint_start();

        for (unsigned j = 0; j < instance->length(); ++j) {
          Literal* const inst_lit = instance->literals()[j];

          // Same-polarity match (subsumption part)
          if (Literal::headersMatch(base_lit, inst_lit, false)) {
            {
              auto binder = theory.start_binder();
              if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
                subsat::Var b = solver.new_variable(i);
                theory.commit_bindings(binder, b);
                solver.constraint_push_literal(b);
                inst_normal_matches[j].push_back(b);
                match_count += 1;
              }
            }
            if (base_lit->commutative()) {
              auto binder = theory.start_binder();
              if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
                subsat::Var b = solver.new_variable(i);
                theory.commit_bindings(binder, b);
                solver.constraint_push_literal(b);
                inst_normal_matches[j].push_back(b);
                match_count += 1;
              }
            }
          }

          // Complementary match (subsumption resolution part)
          if (Literal::headersMatch(base_lit, inst_lit, true)) {
            {
              auto binder = theory.start_binder();
              if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
                subsat::Var b = solver.new_variable(i);
                theory.commit_bindings(binder, b);
                solver.constraint_push_literal(b);
                complementary_matches.push_back({b, j});
                inst_compl_matches[j].push_back(b);
                match_count += 1;
              }
            }
            if (base_lit->commutative()) {
              auto binder = theory.start_binder();
              if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
                subsat::Var b = solver.new_variable(i);
                theory.commit_bindings(binder, b);
                solver.constraint_push_literal(b);
                complementary_matches.push_back({b, j});
                inst_compl_matches[j].push_back(b);
                match_count += 1;
              }
            }
          }
        }

        auto handle = solver.constraint_end();
        solver.add_clause_unsafe(handle);

        // If there are no matches for this base literal, we have just added an empty clause.
        // => conflict on root level due to empty clause, abort early
        if (match_count == 0) {
          return false;
        }
      }

      // NOTE: these constraints are necessary because:
      // 1) when an inst_lit is complementary-matched, then we cannot match anything else to it.
      // 2) but when it is not complementary-matched, then we may match multiple base literals to it.
      // The reason 2) is why we can't simply use instance-AtMostOne constraints like we do for subsumption.
      // Naive solution: use binary clauses "~compl \/ ~normal", more sophisticated: use a helper variable that just means "instance literal is complementary-matched".
      //
      // Example of wrong inference without these constraints:
      // % ***WRONG RESULT OF SUBSUMPTION RESOLUTION***
      // %    base       = 1. ~p(X0,X1,X2,X3,X4) | p(X5,X1,X2,X3,X4) [input]
      // %    instance   = 366. ~neq(X10,X11) | ~neq(X10,s0) | ~neq(X12,X11) | ~neq(X10,X12) | ~neq(X10,X13) | ~neq(X12,s0) | ~neq(X13,X14) | ~neq(X13,X11) | ~neq(X10,X14) | p(X10,X13,X14,s0,s0) [duplicate literal removal 362]
      // % Should NOT be possible but found the following result:
      // %    conclusion = 406. ~neq(X10,X11) | ~neq(X10,s0) | ~neq(X12,X11) | ~neq(X10,X12) | ~neq(X10,X13) | ~neq(X12,s0) | ~neq(X13,X14) | ~neq(X13,X11) | ~neq(X10,X14) [subsumption resolution 366,1]
      for (unsigned j = 0; j < instance->length(); ++j) {
        uint32_t const nnormal = inst_normal_matches[j].size();
        uint32_t const ncompl = inst_compl_matches[j].size();
        if (nnormal >= 2 && ncompl >= 2 && nnormal + ncompl > 4) {
          // TODO: more sophisticated encoding with helper variable? instead of the 'matrix' encoding below
          RSTAT_CTR_INC("would do SR sophisticated encoding");
        }
        // Idea: instance literal is complementary-matched => cannot be normal-matched
        // basic implementation using binary clauses.
        for (subsat::Var const b_compl : inst_compl_matches[j]) {
          for (subsat::Var const b_normal : inst_normal_matches[j]) {
            solver.constraint_start();
            solver.constraint_push_literal(~b_compl);
            solver.constraint_push_literal(~b_normal);
            auto handle = solver.constraint_end();
            solver.add_clause_unsafe(handle);
          }
        }
      }

      // At least one complementary match
      // NOTE: this clause is required. Without it, we may get a false subsumption
      //       (because subsumption resolution uses set-matching and not multiset-matching)
      solver.constraint_start();
      for (auto const pair : complementary_matches) {
        subsat::Var const b = pair.first;
        solver.constraint_push_literal(b);
      }
      auto handle = solver.constraint_end();
      solver.add_clause_unsafe(handle);

      // inst_is_compl_matched[j] is true if instance[j] is complementary-matched by one or more base literals
      // (other direction not required, but we could use it instead of the "at least one complementary match" above)
      for (unsigned j = 0; j < instance->length(); ++j) {
        subsat::Var const b_is_matched = solver.new_variable();
        inst_is_compl_matched.push_back(b_is_matched);
        ASS_EQ(inst_is_compl_matched[j], b_is_matched);
        for (subsat::Var const b_compl : inst_compl_matches[j]) {
          solver.constraint_start();
          solver.constraint_push_literal(~b_compl);
          solver.constraint_push_literal(b_is_matched);
          auto handle = solver.constraint_end();
          solver.add_clause_unsafe(handle);
        }
      }

      // At most one instance literal is complementary-matched.
      // But note that this instance literal may be complementary-matched by multiple base literals!
      solver.constraint_start();
      for (subsat::Var const b_is_matched : inst_is_compl_matched) {
        solver.constraint_push_literal(b_is_matched);
      }
      auto handle2 = solver.constraint_end();
      solver.add_atmostone_constraint_unsafe(handle2);

      // // TODO: this is wrong. what we actually want is that at most one *INSTANCE LITERAL* is complementary-matched.
      // //       but it may be complementary-matched by multiple base literals (and this case is quite common, actually)
      // // At most one complementary match
      // solver.constraint_start();
      // for (auto const pair : complementary_matches) {
      //   subsat::Var const b = pair.first;
      //   solver.constraint_push_literal(b);
      // }
      // auto handle2 = solver.constraint_end();
      // solver.add_atmostone_constraint_unsafe(handle2);

      return !solver.inconsistent();
      // TODO: second version that transforms the subsumption instance into an SR instance?
      //       Why? because ForwardSubsumptionAndResolution does something similar with caching the ClauseMatches structure.
      //       However, we would have to cache the whole solver. Do we want to do this?
      //       No, actually we could also re-use the matches (store the matches separately and just cache that).
    }  // setupSubsumptionResolution


    /// Solve the subsumption instance created by the previous call to a setup... function.
    bool solve()
    {
      CALL("SMTSubsumptionImpl2::solve");
      return solver.solve() == subsat::Result::Sat;
    }

    /// Call this function after solve() has returned true for an SR instance
    Kernel::Clause* getSubsumptionResolutionConclusion()
    {
      int const conclusion_len = m_instance->length() - 1;
      Clause* conclusion = new (conclusion_len) Clause(conclusion_len,
          SimplifyingInference2(InferenceRule::SUBSUMPTION_RESOLUTION, m_instance, m_base));

      std::uint32_t resolved_idx = UINT32_MAX;
      for (auto const pair : complementary_matches) {
        subsat::Var const b = pair.first;
        if (solver.get_value(b) == subsat::Value::True) {
          resolved_idx = pair.second;
          break;
        }
      }
      ASS_NEQ(resolved_idx, UINT32_MAX);
      Literal* const resolved_lit = m_instance->literals()[resolved_idx];

      unsigned next = 0;
      for (unsigned i = 0; i < m_instance->length(); ++i) {
        Literal* const lit = m_instance->literals()[i];
        if (lit != resolved_lit) {
          (*conclusion)[next++] = lit;
        }
      }
      ASS_EQ(next, conclusion_len);
      return conclusion;
    }

    bool checkClauseEquality(Clause* const cl1, Clause* const cl2)
    {
      return checkClauseEquality(cl1->literals(), cl1->length(), cl2->literals(), cl2->length());
    }

    bool checkClauseEquality(Literal const* const lits1[], unsigned len1, Literal const* const lits2[], unsigned len2)
    {
      if (len1 != len2) {
        return false;
      }
      // Copy given literals so we can sort them
      vvector<Literal const*> c1(lits1, lits1 + len1);
      vvector<Literal const*> c2(lits2, lits2 + len2);
      // The equality tests only make sense for shared literals
      std::for_each(c1.begin(), c1.end(), [](Literal const* lit) { ASS(lit->shared()); });
      std::for_each(c2.begin(), c2.end(), [](Literal const* lit) { ASS(lit->shared()); });
      // Sort input by pointer value
      // NOTE: we use std::less<> because the C++ standard guarantees it is a total order on pointer types.
      //       (the built-in operator< is not required to be a total order for pointer types.)
      std::less<Literal const*> const lit_ptr_less{};
      std::sort(c1.begin(), c1.end(), lit_ptr_less);
      std::sort(c2.begin(), c2.end(), lit_ptr_less);
      // Finally check the equality
      return c1 == c2;
    }

    bool checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance)
    {
      CALL("SMTSubsumptionImpl2::checkSubsumption");
      return setupSubsumption(base, instance) && solve();
    }

    /// For correctness checking: if the original subsumption resolution finds a conclusion, call this to check whether we can also find this conclusion.
    /// Note that SR is not unique, so there could be multiple possible conclusions, and both approaches may return a different one.
    ///
    /// Example for multiple possible subsumption resolutions:
    ///     base = P(x) \/ Q(x) \/ R(x)
    ///     inst = P(c) \/ Q(c) \/ ~R(c) \/ P(d) \/ ~Q(d) \/ R(d)
    ///
    /// Pass NULL for the conclusion to check that subsumption resolution isn't possible.
    bool checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* conclusion)
    {
      setupSubsumptionResolution(base, instance);
      if (conclusion == nullptr) {
        RSTAT_CTR_INC("failed subsumption resolutions");
        if (solve()) {
          std::cerr << "\% ***WRONG RESULT OF SUBSUMPTION RESOLUTION***" << std::endl;
          std::cerr << "\%    base       = " << base->toString() << std::endl;
          std::cerr << "\%    instance   = " << instance->toString() << std::endl;
          std::cerr << "\% Should NOT be possible but SMT-SR found the following result:" << std::endl;
          std::cerr << "\%    conclusion = " << getSubsumptionResolutionConclusion()->toString() << std::endl;
          return false;
        } else {
          return true;
        }
      }
      int found = 0;
      while (solve()) {
        // Found another model, build the corresponding result
        Kernel::Clause* cl = getSubsumptionResolutionConclusion();
        if (checkClauseEquality(cl, conclusion)) {
          found += 1;
        }
      }
      RSTAT_MCTR_INC("subsumption resolution #possible consequences", found);
      if (found == 0) {
        std::cerr << "\% ***WRONG RESULT OF SUBSUMPTION RESOLUTION***" << std::endl;
        std::cerr << "\%    base     = " << base->toString() << std::endl;
        std::cerr << "\%    instance = " << instance->toString() << std::endl;
        std::cerr << "\% No result from SMT-SR, but should have found this conclusion:" << std::endl;
        std::cerr << "\%    expected = " << conclusion->toString() << std::endl;
      }
      return (found > 0);
    }
};  // class SMTSubsumptionImpl2



class SMTSubsumption::SMTSubsumptionImpl3
{
  private:

#if 1
    template <typename T>
    using allocator_type = STLAllocator<T>;
#else
    template <typename T>
    using allocator_type = std::allocator<T>;
#endif

    subsat::Solver<allocator_type> solver;

    Kernel::Clause* instance = nullptr;   // main premise for forward subsumption (resolution)

    /// AtLeastOne constraints stating that each base literal may be matched at least once.
    /// Since we allocate SAT variables consecutively, we only need to store the length of each of these clauses.
    vvector<uint32_t> base_clauses;

    /// AtMostOne constraints stating that each instance literal may be matched at most once.
    vvector<subsat::AllocatedConstraintHandle> instance_constraints;

  public:
    CLASS_NAME(SMTSubsumptionImpl3);
    USE_ALLOCATOR(SMTSubsumptionImpl3);

    SMTSubsumptionImpl3()
    {
      solver.reserve_variables(64);
      solver.reserve_clause_storage(512);
      solver.theory().reserve(64, 2, 16);
      base_clauses.reserve(16);
      instance_constraints.reserve(16);
    }

    void setupMainPremise(Kernel::Clause* new_instance)
    {
      instance = new_instance;
      // TODO:
      // Copy the literals into a vvector, std::sort them (like LiteralMiniIndex; by header).
      // Then use std::binary_search to find the first one in setupSubsumption?
    }

    /// Set up the subsumption problem. Must have called setupMainPremise first.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumption(Kernel::Clause* base)
    {
      solver.clear();
      ASS(solver.empty());
      auto& theory = solver.theory();
      ASS(theory.empty());

      uint32_t const base_len = base->length();
      uint32_t const inst_len = instance->length();

      base_clauses.clear();
      ASS(base_clauses.empty());

      // Here we store the AtMostOne constraints saying that each instance literal may be matched at most once.
      // Each instance literal can be matched by at most 2 boolean vars per base literal (two orientations of equalities).
      // NOTE: instance constraints cannot be packed densely because we only know their shape at the end.
      uint32_t const instance_constraint_maxsize = 2 * base_len;
      instance_constraints.clear();
      ASS(instance_constraints.empty());
      for (size_t i = 0; i < instance->length(); ++i) {
        instance_constraints.push_back(solver.alloc_constraint(instance_constraint_maxsize));
      }

      // Pre-matching
      // To keep overhead as low as possible, we do not yet create solver variables at this point
      uint32_t nextVarIndex = 0;
      for (unsigned bi = 0; bi < base->length(); ++bi) {
        Literal* base_lit = base->literals()[bi];
        uint32_t match_count = 0;

        for (unsigned j = 0; j < instance->length(); ++j) {
          Literal* inst_lit = instance->literals()[j];

          if (!Literal::headersMatch(base_lit, inst_lit, false)) {
            continue;
          }

          {
            auto binder = theory.start_binder();
            if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
              subsat::Var b{nextVarIndex++};
              // LOG_DEBUG("MatchFwd: " << b << " ~ " << base_lit->toString() << " -> " << inst_lit->toString());
              match_count += 1;
              theory.commit_bindings(binder, b);
              solver.handle_push_literal(instance_constraints[j], b);
            }
          }

          if (base_lit->commutative()) {
            ASS_EQ(base_lit->arity(), 2);
            ASS_EQ(inst_lit->arity(), 2);
            auto binder = theory.start_binder();
            if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
              subsat::Var b{nextVarIndex++};
              // LOG_DEBUG("MatchRev: " << b << " ~ " << base_lit->toString() << " -> " << inst_lit->toString());
              match_count += 1;
              theory.commit_bindings(binder, b);
              solver.handle_push_literal(instance_constraints[j], b);
            }
          }
        }
        base_clauses.push_back(match_count);

        // If there are no matches for this base literal, we will add an empty clause.
        // => conflict on root level due to empty clause, abort early
        if (match_count == 0) {
          return false;
        }
      }

      // Build clauses stating that base_lit must be matched to at least one corresponding instance literal.
      ASS_EQ(base_clauses.size(), base->length());
      for (unsigned bi = 0; bi < base->length(); ++bi) {
        uint32_t match_count = base_clauses[bi];
        solver.constraint_start();
        while (match_count--) {
          subsat::Var b = solver.new_variable(bi);
          solver.constraint_push_literal(b);
        }
        auto handle = solver.constraint_end();
        solver.add_clause_unsafe(handle);
      }

      for (auto handle : instance_constraints) {
        auto built = solver.handle_build(handle);
        solver.add_atmostone_constraint_unsafe(built);
      }

      return !solver.inconsistent();
    }  // setupSubsumption

    /// Set up the subsumption resolution problem. Must have called setupMainPremise first.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setupSubsumptionResolution(Kernel::Clause* base)
    {
      // TODO
    }  // setupSubsumptionResolution

    bool solve()
    {
      return solver.solve() == subsat::Result::Sat;
    }

};  // class SMTSubsumptionImpl3



/****************************************************************************/
/****************************************************************************/
/****************************************************************************/










/****************************************************************************
 * --mode stest
 ****************************************************************************/

void ProofOfConcept::test(Clause* side_premise, Clause* main_premise)
{
  CALL("ProofOfConcept::test");
  std::cout << "\% SMTSubsumption::test" << std::endl;
  std::cout << "\% side_premise: " << side_premise->toString() << std::endl;
  std::cout << "\% main_premise: " << main_premise->toString() << std::endl;
  std::cout << std::endl;
  BYPASSING_ALLOCATOR;

  {
    SMTSubsumptionImpl2 impl;
    std::cout << "\nTESTING 'subsat' subsumption (v2)" << std::endl;
    subsat::print_config(std::cout);
    std::cout << "SETUP" << std::endl;
    bool subsumed1 = impl.setupSubsumption(side_premise, main_premise);
    std::cout << "  => " << subsumed1 << std::endl;
    std::cout << "SOLVE" << std::endl;
    bool subsumed = subsumed1 && impl.solve();
    std::cout << "  => " << subsumed << std::endl;
  }

  {
    SMTSubsumptionImpl3 impl;
    std::cout << "\nTESTING 'subsat' subsumption (v3)" << std::endl;
    subsat::print_config(std::cout);
    std::cout << "SETUP" << std::endl;
    impl.setupMainPremise(main_premise);
    bool subsumed1 = impl.setupSubsumption(side_premise);
    std::cout << "  => " << subsumed1 << std::endl;
    std::cout << "SOLVE" << std::endl;
    bool subsumed = subsumed1 && impl.solve();
    std::cout << "  => " << subsumed << std::endl;
  }

  {
    std::cout << "\nTESTING 'MLMatcher'" << std::endl;
    OriginalSubsumption::Impl orig;
    bool subsumed = orig.checkSubsumption(side_premise, main_premise);
    std::cout << "  => " << subsumed << std::endl;
    // if (subsumed != expected_subsumed) {
    //   std::cout << "UNEXPECTED RESULT: " << subsumed << std::endl;
    // }
    orig.printStats(std::cout);
  }

  {
    SMTSubsumptionImpl2 impl;
    std::cout << "\nTESTING 'subsat' subsumption resolution (v2)" << std::endl;
    subsat::print_config(std::cout);
    std::cout << "SETUP" << std::endl;
    bool res1 = impl.setupSubsumptionResolution(side_premise, main_premise);
    std::cout << "  => " << res1 << std::endl;
    std::cout << "SOLVE" << std::endl;
    bool res = res1 && impl.solve();
    std::cout << "  => " << res << std::endl;
    std::cout << "conclusion = " << impl.getSubsumptionResolutionConclusion()->toString() << std::endl;
  }
}

ProofOfConcept::ProofOfConcept()
{
  m_subsat_impl.reset(new SMTSubsumptionImpl2());
  m_subsat_impl3.reset(new SMTSubsumptionImpl3());
}

ProofOfConcept::~ProofOfConcept() = default;

bool ProofOfConcept::checkSubsumption(Kernel::Clause* base, Kernel::Clause* instance)
{
  CALL("ProofOfConcept::checkSubsumption");
  ASS(m_subsat_impl);
  return m_subsat_impl->checkSubsumption(base, instance);
}

bool ProofOfConcept::checkSubsumptionResolution(Kernel::Clause* base, Kernel::Clause* instance, Kernel::Clause* conclusion)
{
  CALL("ProofOfConcept::checkSubsumptionResolution");
  ASS(m_subsat_impl);
  return m_subsat_impl->checkSubsumptionResolution(base, instance, conclusion);
}


void ProofOfConcept::setupMainPremise(Kernel::Clause* instance)
{
  ASS(m_subsat_impl3);
  m_subsat_impl3->setupMainPremise(instance);
}

bool ProofOfConcept::setupSubsumption(Kernel::Clause* base)
{
  ASS(m_subsat_impl3);
  return m_subsat_impl3->setupSubsumption(base);
}

bool ProofOfConcept::solve()
{
  ASS(m_subsat_impl3);
  return m_subsat_impl3->solve();
}




/****************************************************************************
 * Benchmarks
 ****************************************************************************/


#if ENABLE_BENCHMARK
// Google benchmark library
// https://github.com/google/benchmark
#include <benchmark/benchmark.h>
#endif  // ENABLE_BENCHMARK


#if ENABLE_BENCHMARK

template<typename It>
struct Iterable {
  It m_begin;
  It m_end;
  It begin() const { return m_begin; }
  It end() const { return m_end; }
};

class FwSubsumptionRound
{
public:
  using s_iter = vvector<SubsumptionInstance>::const_iterator;
  using sr_iter = vvector<SubsumptionResolutionInstance>::const_iterator;
  Iterable<s_iter> subsumptions() const { return {s_begin, s_end}; }
  Iterable<sr_iter> subsumptionResolutions() const { return {sr_begin, sr_end}; }
  Kernel::Clause* main_premise() const { return m_main_premise; }

  FwSubsumptionRound(SubsumptionBenchmark const& b, size_t round) {
    size_t s_begin_idx = (round == 0) ? 0 : b.rounds[round-1].s_end;
    size_t s_end_idx = (round < b.rounds.size()) ? b.rounds[round].s_end : b.subsumptions.size();
    size_t sr_begin_idx = (round == 0) ? 0 : b.rounds[round-1].sr_end;
    size_t sr_end_idx = (round < b.rounds.size()) ? b.rounds[round].sr_end : b.subsumptionResolutions.size();
    s_begin = b.subsumptions.begin() + s_begin_idx;
    s_end = b.subsumptions.begin() + s_end_idx;
    sr_begin = b.subsumptionResolutions.begin() + sr_begin_idx;
    sr_end = b.subsumptionResolutions.begin() + sr_end_idx;

    if (s_begin != s_end) {
      m_main_premise = s_begin->main_premise;
    }
    else if (sr_begin != sr_end) {
      m_main_premise = sr_begin->main_premise;
    }
    else {
      m_main_premise = nullptr;
    }
    ASS(std::all_of(s_begin, s_end, [this](auto const& s){ return s.main_premise == m_main_premise; }));
    ASS(std::all_of(sr_begin, sr_end, [this](auto const& sr){ return sr.main_premise == m_main_premise; }));
  }

  FwSubsumptionRound withoutSubsumptionResolution() const {
    FwSubsumptionRound r = *this;
    r.sr_end = r.sr_begin;
    return r;
  }

private:
  Kernel::Clause* m_main_premise;  ///< also called "instance clause"
  s_iter s_begin;
  s_iter s_end;
  sr_iter sr_begin;
  sr_iter sr_end;
};


void bench_smt2_run_setup(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {
    SMTSubsumptionImpl2 impl;
    int count = 0;
    for (auto const& round : fw_rounds) {
      Kernel::Clause::requestAux();
      Kernel::Clause* main_premise = round.main_premise();
      for (auto const& s : round.subsumptions()) {
        if (!impl.setupSubsumption(s.side_premise, main_premise)) {
          count++;
          if (s.result > 0) { state.SkipWithError("Wrong result!"); Kernel::Clause::releaseAux(); return; }
        }
        // no solve since we only measure the setup
      }
      for (auto const& sr : round.subsumptionResolutions()) {
        if (sr.side_premise->hasAux())
          continue;
        sr.side_premise->setAux(nullptr);  // other than original SR we only need to handle each side premise once
        if (!impl.setupSubsumptionResolution(sr.side_premise, main_premise)) {
          count++;
          // can't check result here because the logged result might cover only one resLit.
          // if (sr.result > 0) { state.SkipWithError("Wrong result!"); return; }
        }
        // no solve since we only measure the setup
      }
      Kernel::Clause::releaseAux();
    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}

void bench_smt2_run(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {
    SMTSubsumptionImpl2 impl;
    int count = 0;
    for (auto const& round : fw_rounds) {
      Kernel::Clause::requestAux();
      Kernel::Clause* main_premise = round.main_premise();
      for (auto const& s : round.subsumptions()) {
        bool res = impl.setupSubsumption(s.side_premise, main_premise) && impl.solve();
        if (s.result >= 0 && res != s.result) {
          state.SkipWithError("Wrong result!");
          Kernel::Clause::releaseAux();
          return;
        }
        count += res;
      }
      for (auto const& sr : round.subsumptionResolutions()) {
        if (sr.side_premise->hasAux())
          continue;
        sr.side_premise->setAux(nullptr);  // other than original SR we only need to handle each side premise once
        bool res = impl.setupSubsumptionResolution(sr.side_premise, main_premise) && impl.solve();
        // can't check result here because the logged result might cover only one resLit.
        count += res;
      }
      Kernel::Clause::releaseAux();
    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}
void bench_smt3_fwrun_setup(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {
    int count = 0;  // counter to introduce data dependency which should prevent compiler optimization from removing code

    SMTSubsumptionImpl3 impl;
    for (auto const& round : fw_rounds) {
      Clause::requestAux();
      // Set up main premise
      impl.setupMainPremise(round.main_premise());
      // Test subsumptions
      for (auto const& s : round.subsumptions()) {
        if (!impl.setupSubsumption(s.side_premise)) {
          count++;
          if (s.result > 0) { state.SkipWithError("Wrong result!"); Kernel::Clause::releaseAux(); return; }
        }
        // not solve since we only measure the setup
      }
      // TODO: SR... what exactly do we want to measure here?
      for (auto const& sr : round.subsumptionResolutions()) {
        state.SkipWithError("Subsumption Resolution not yet implemented");
      }
      Clause::releaseAux();
    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}

void bench_smt3_fwrun(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {
    int count = 0;  // counter to introduce data dependency which should prevent compiler optimization from removing code

    SMTSubsumptionImpl3 impl;

    for (auto const& round : fw_rounds) {
      Clause::requestAux();
      // Set up main premise
      impl.setupMainPremise(round.main_premise());
      // Test subsumptions
      for (auto const& s : round.subsumptions()) {
        bool const subsumed = impl.setupSubsumption(s.side_premise) && impl.solve();
        if (s.result >= 0 && subsumed != s.result) {
          state.SkipWithError("Wrong result!");
          Kernel::Clause::releaseAux();
          return;
        }
        if (subsumed) { count++; }  // NOTE: since we record subsumption log from a real fwsubsumption run, this will only happen at the last iteration.
      }
      // Test subsumption resolutions
      for (auto const& sr : round.subsumptionResolutions()) {
        bool const result = impl.setupSubsumptionResolution(sr.side_premise) && impl.solve();
        if (sr.result >= 0 && result != sr.result) {
          state.SkipWithError("Wrong result!");
          Kernel::Clause::releaseAux();
          return;
        }
        if (result) { count++; }  // NOTE: since we record subsumption log from a real fwsubsumption run, this will only happen at the last iteration.
      }
      Clause::releaseAux();
    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}

void bench_orig_fwrun_setup(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {

    int count = 0;  // counter to introduce data dependency which should prevent compiler optimization from removing code

    using namespace OriginalSubsumption;
    using CMStack = Stack<ClauseMatches*>;

    // the static variables from the original implementation
    Kernel::MLMatcher matcher;
    CMStack cmStore{64};

    for (auto const& round : fw_rounds) {
      Clause::requestAux();

      // Set up main premise
      ASS(cmStore.isEmpty());
      Kernel::Clause* cl = round.main_premise();

      LiteralMiniIndex miniIndex(cl);

      // Test subsumptions
      for (auto const& s : round.subsumptions()) {
        Clause* mcl = s.side_premise;
        unsigned mlen = mcl->length();

        ClauseMatches* cms = new ClauseMatches(mcl);  // NOTE: why "new" here? because the original code does it like this as well.
        cmStore.push(cms);
        cms->fillInMatches(&miniIndex);

        if (cms->anyNonMatched()) {
          // NOT SUBSUMED
          count++;
          if (s.result > 0) { state.SkipWithError("Wrong result!"); Kernel::Clause::releaseAux(); return; }
          continue;
        }

        // nothing to do here, since we only want to measure the setup.
      }

      // TODO: SR... what exactly do we want to measure here?
      for (auto const& sr : round.subsumptionResolutions()) {
        state.SkipWithError("Subsumption Resolution not yet implemented");
      }

      // Cleanup
      Clause::releaseAux();
      while (cmStore.isNonEmpty()) {
        delete cmStore.pop();
      }

    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}

void bench_orig_fwrun(benchmark::State& state, vvector<FwSubsumptionRound> const& fw_rounds)
{
  for (auto _ : state) {

    int count = 0;  // counter to introduce data dependency which should prevent compiler optimization from removing code

    using namespace OriginalSubsumption;
    using CMStack = Stack<ClauseMatches*>;

    // the static variables from the original implementation
    Kernel::MLMatcher matcher;
    CMStack cmStore{64};

    for (auto const& round : fw_rounds) {
      Clause::requestAux();

      // Set up main premise
      ASS(cmStore.isEmpty());
      Kernel::Clause* cl = round.main_premise();

      LiteralMiniIndex miniIndex(cl);

      // Test subsumptions
      for (auto const& s : round.subsumptions()) {
        Clause* mcl = s.side_premise;
        unsigned mlen = mcl->length();

        ClauseMatches* cms = new ClauseMatches(mcl);  // NOTE: why "new" here? because the original code does it like this as well.
        cmStore.push(cms);
        cms->fillInMatches(&miniIndex);
        mcl->setAux(cms);

        if (cms->anyNonMatched()) {
          // NOT SUBSUMED
          if (s.result > 0) { state.SkipWithError("Wrong result!"); Kernel::Clause::releaseAux(); return; }
          continue;
        }

        matcher.init(mcl, cl, cms->_matches, true);
        bool const subsumed = matcher.nextMatch();
        if (s.result >= 0 && subsumed != s.result) {
          state.SkipWithError("Wrong result!");
          Kernel::Clause::releaseAux();
          return;
        }
        if (subsumed) { count++; }  // NOTE: since we record subsumption log from a real fwsubsumption run, this will only happen at the last iteration anyway.
      }

      // Test subsumption resolutions
      for (auto const& sr : round.subsumptionResolutions()) {
        Clause* mcl = sr.side_premise;
        ClauseMatches* cms = nullptr;
        if (mcl->hasAux()) {
          cms = mcl->getAux<ClauseMatches>();
        }
        if (!cms) {
          cms = new ClauseMatches(mcl);
          mcl->setAux(cms);
          cmStore.push(cms);
          cms->fillInMatches(&miniIndex);
        }
        if (sr.res_lit == UINT_MAX) {
          ASS(mcl->hasAux());
          for (unsigned li = 0; li < cl->length(); li++) {
            Literal* resLit = (*cl)[li];
            bool result = checkForSubsumptionResolution(cl, cms, resLit);
            // note: in this case the result is only logged for the first res_lit.
            if (li == 0 && sr.result >= 0 && result != sr.result) {
              state.SkipWithError("Wrong SR result (1)!");
              Kernel::Clause::releaseAux();
              return;
            }
            if (result) { count++; }
          }
        } else {
          Literal* resLit = (*cl)[sr.res_lit];
          bool result = checkForSubsumptionResolution(cl, cms, resLit);
          if (sr.result >= 0 && result != sr.result) {
            state.SkipWithError("Wrong SR result (2)!");
            Kernel::Clause::releaseAux();
            return;
          }
          if (result) { count++; }
        }
      }

      // Cleanup
      Clause::releaseAux();
      while (cmStore.isNonEmpty()) {
        delete cmStore.pop();
      }

    }
    benchmark::DoNotOptimize(count);
    benchmark::ClobberMemory();
  }
}



void ProofOfConcept::benchmark_run(SubsumptionBenchmark b)
{
  CALL("ProofOfConcept::benchmark_run");
  BYPASSING_ALLOCATOR;  // google-benchmark needs its own memory

  std::cerr << "\% SMTSubsumption: benchmarking " << b.subsumptions.size() << " S and " << b.subsumptionResolutions.size() << " SR" << std::endl;
#if VDEBUG
  std::cerr << "\n\n\nWARNING: compiled in debug mode!\n\n\n" << std::endl;
#endif

  vvector<FwSubsumptionRound> fw_rounds;
  for (size_t round = 0; round <= b.rounds.size(); ++round) {
    fw_rounds.emplace_back(b, round);
  }
  // pop empty round at the end
  if (!fw_rounds.back().main_premise()) {
    fw_rounds.pop_back();
  }
  // all remaining ones should be non-empty
  ASS(std::all_of(fw_rounds.begin(), fw_rounds.end(), [](auto const& r) { return !!r.main_premise(); }));

  vvector<FwSubsumptionRound> fw_rounds_only_subsumption;
  for (auto const& r : fw_rounds) {
    fw_rounds_only_subsumption.push_back(r.withoutSubsumptionResolution());
  }

  vvector<vstring> args = {
    "vampire-sbench-run",
    // "--help",
  };

  benchmark::RegisterBenchmark("smt2 S    (setup)", bench_smt2_run_setup, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("smt2 S    (full)", bench_smt2_run, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("smt2 S+SR (setup)", bench_smt2_run_setup, fw_rounds);
  benchmark::RegisterBenchmark("smt2 S+SR (full)", bench_smt2_run, fw_rounds);

  benchmark::RegisterBenchmark("smt3 S    (setup)", bench_smt3_fwrun_setup, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("smt3 S    (full)", bench_smt3_fwrun, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("smt3 S+SR (setup)", bench_smt3_fwrun_setup, fw_rounds);
  benchmark::RegisterBenchmark("smt3 S+SR (full)", bench_smt3_fwrun, fw_rounds);

  benchmark::RegisterBenchmark("orig S    (setup)", bench_orig_fwrun_setup, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("orig S    (full)", bench_orig_fwrun, fw_rounds_only_subsumption);
  benchmark::RegisterBenchmark("orig S+SR (setup)", bench_orig_fwrun_setup, fw_rounds);
  benchmark::RegisterBenchmark("orig S+SR (full)", bench_orig_fwrun, fw_rounds);

  init_benchmark(std::move(args));
  benchmark::RunSpecifiedBenchmarks();
  std::cerr << "Benchmarking done, shutting down..." << std::endl;
  Kernel::Clause::requestAux();
  Kernel::Clause::releaseAux();
}

#else

void ProofOfConcept::benchmark_run(vvector<SubsumptionInstance> instances)
{
  CALL("ProofOfConcept::benchmark_run");
  USER_ERROR("compiled without benchmarking!");
}

#endif  // ENABLE_BENCHMARK


// Example commutativity:
// side: f(x) = y
// main: f(d) = f(e)
// possible matchings:
// - x->d, y->f(e)
// - x->e, y->f(d)

// Example by Bernhard re. problematic subsumption demodulation:
// side: x1=x2 or x3=x4 or x5=x6 or x7=x8
// main: x9=x10 or x11=x12 or x13=14 or P(t)


// TODO: subsumption resolution
// maybe we can extend the subsumption instance easily?
// Add a flag (i.e., a boolean variable that's to be used as assumption)
//  to switch between subsumption and subsumption resolution.
// But other SR-clauses are only generated after checking S.







void ProofOfConcept::benchmark_micro(SubsumptionBenchmark b)
{
  CALL("ProofOfConcept::benchmark_micro");
  BYPASSING_ALLOCATOR;  // google-benchmark needs its own memory
  std::cerr << "obsolete mode\n";
  std::exit(1);
}
