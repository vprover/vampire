#include "SMTSubsumption.hpp"
#include "SubstitutionTheory.hpp"
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

#include <chrono>
#include <iostream>
#include <iomanip>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;

#include "SMTSubsumption/cdebug.hpp"


#define ENABLE_BENCHMARK 1



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


class OriginalSubsumptionImpl
{
  private:
    Kernel::MLMatcher matcher;
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
      // ASS_G(mlen,1);   // (not really necessary for the benchmarks)

      ClauseMatches* cms = new ClauseMatches(mcl);
      cms->fillInMatches(&miniIndex);

      if (cms->anyNonMatched()) {
        return false;
      }

      matcher.init(mcl, cl, cms->_matches, true);
      return true;
    }

    bool solve()
    {
      bool isSubsumed = matcher.nextMatch();
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

          VectorStoringBinder binder(bindings_storage);
          if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
            Minisat::Var b = nextVar++;

            if (binder.size() > 0) {
              ASS(!base_lit->ground());
            } else {
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
          }

          if (base_lit->commutative()) {
            ASS_EQ(base_lit->arity(), 2);
            ASS_EQ(inst_lit->arity(), 2);
            binder.reset();
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
        Minisat::Clause* c1 = reinterpret_cast<Minisat::Clause*>(&clause_storage[c_index]);
        Minisat::AtMostOne* c2 = reinterpret_cast<Minisat::AtMostOne*>(&clause_storage[c_index]);
        ASS(!c1->learnt());
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
      out << "Conflicts:    " << std::setw(8) << solver.stats.conflicts << std::endl;
      out << "Propagations: " << std::setw(8) << solver.stats.propagations << std::endl;
    }

    /// Set up the subsumption problem.
    /// Returns false if no solution is possible.
    /// Otherwise, solve() needs to be called.
    bool setup(Kernel::Clause* side_premise, Kernel::Clause* main_premise, Minisat::VarOrderStrategy vo_strategy = Minisat::VarOrderStrategy::MinisatDefault)
    {
      CDEBUG("SMTSubsumptionImpl::setup()");
      // solver.reset();  // TODO
      // solver.verbosity = 2;  // maybe only for debug...

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
 * --mode stest
 ****************************************************************************/

void ProofOfConcept::test(Clause* side_premise, Clause* main_premise)
{
  CALL("ProofOfConcept::test");
  std::cout << "\% SMTSubsumption::test" << std::endl;
  std::cout << "\% side_premise: " << side_premise->toString() << std::endl;
  std::cout << "\% main_premise: " << main_premise->toString() << std::endl;
  std::cout << std::endl;

  static_assert(alignof(Minisat::Solver) == 8, "");
  static_assert(alignof(Minisat::Solver *) == 8, "");
  static_assert(alignof(Minisat::Clause) == 4, "");
  static_assert(alignof(Minisat::Clause *) == 8, "");
  static_assert(sizeof(Minisat::Clause) == 8, "");
  static_assert(sizeof(Minisat::Clause *) == 8, "");

  {
    using Minisat::index;
    using Minisat::Lit;
    uint32_t storage[] = {
      27,
      5,
      (uint32_t)index(Lit(1)),
      (uint32_t)index(Lit(2)),
      (uint32_t)index(Lit(7)),
      (uint32_t)index(~Lit(8)),
      (uint32_t)index(Lit(13)),
    };
    Minisat::AtMostOne* c2 = reinterpret_cast<Minisat::AtMostOne*>(&storage[1]);
    ASS_EQ(c2->size(), 5);
    ASS_EQ((*c2)[0], Lit(1));
    ASS_EQ((*c2)[3], ~Lit(8));
    Minisat::Clause* c1 = reinterpret_cast<Minisat::Clause*>(&storage[1]);
    ASS(!c1->learnt());
    ASS_EQ(c1->size(), 5);
    ASS_EQ((*c1)[0], Lit(1));
    ASS_EQ((*c1)[3], ~Lit(8));
  }

  SMTSubsumptionImpl impl;
  std::cout << "SETUP" << std::endl;
  bool subsumed1 = impl.setup2(side_premise, main_premise);
  std::cout << "  => " << subsumed1 << std::endl;
  std::cout << "SOLVE" << std::endl;
  bool subsumed = subsumed1 && impl.solve();
  std::cout << "  => " << subsumed << std::endl;
  return;

  std::pair<char const*, Minisat::VarOrderStrategy> vo_strategies[] = {
      { "MinisatDefault", Minisat::VarOrderStrategy::MinisatDefault },
      { "RemainingChoices", Minisat::VarOrderStrategy::RemainingChoices },
      { "10% RemainingChoices, rest activity", Minisat::VarOrderStrategy::Alternate_10 },
      { "50% RemainingChoices, rest activity", Minisat::VarOrderStrategy::Alternate_50 },
      { "80% RemainingChoices, rest activity", Minisat::VarOrderStrategy::Alternate_80 },
      { "RemainingChoices / (activity + 1) [per-boolean activity]", Minisat::VarOrderStrategy::CombinedBoolAct_k1 },
      { "RemainingChoices / (activity + 3) [per-boolean activity]", Minisat::VarOrderStrategy::CombinedBoolAct_k3 },
      { "RemainingChoices / (activity + 5) [per-boolean activity]", Minisat::VarOrderStrategy::CombinedBoolAct_k5 },
  };
  for (auto p : vo_strategies) {
    auto vo_strategy_name = p.first;
    auto vo_strategy = p.second;

    SMTSubsumptionImpl impl;
    std::cout << "SMTSubsumption with vo_strategy = " << vo_strategy_name << std::endl;
    bool subsumed = impl.setup(side_premise, main_premise, vo_strategy) && impl.solve();
    std::cout << "Subsumed: " << subsumed << std::endl;
    impl.printStats(std::cout);

    std::cout << std::endl;
  }

  std::cout << "MLMatcher" << std::endl;
  OriginalSubsumption::Impl orig;
  std::cout << "MLMatcher says: " << orig.checkSubsumption(side_premise, main_premise) << std::endl;
  orig.printStats(std::cout);
}

bool ProofOfConcept::checkSubsumption(Kernel::Clause *side_premise, Kernel::Clause *main_premise)
{
  SMTSubsumptionImpl impl;
  return impl.checkSubsumption(side_premise, main_premise);
}





/****************************************************************************
 * Benchmarks
 ****************************************************************************/


static void escape(void* p) {
  asm volatile("" : : "g"(p) : "memory");
}

static void clobber() {
  asm volatile("" : : : "memory");
}

#include <atomic>
#include <x86intrin.h>

uint64_t rdtscp()
{
  std::atomic_signal_fence(std::memory_order_acq_rel);
  uint32_t aux = 0;
  uint64_t result = __rdtscp(&aux);
  std::atomic_signal_fence(std::memory_order_acq_rel);
  return result;
}





#if ENABLE_BENCHMARK
// Google benchmark library
// https://github.com/google/benchmark
#include <benchmark/benchmark.h>


void bench_smt_total(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    SMTSubsumptionImpl smt_impl;
    bool smt_result = smt_impl.checkSubsumption(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(smt_result);
    if (smt_result != instance.subsumed) {
      state.SkipWithError("Wrong result!");
      return;
    }
  }
}

void bench_smt_setup(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    SMTSubsumptionImpl smt_impl;
    bool smt_setup_result = smt_impl.setup(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(smt_setup_result);
    benchmark::ClobberMemory();
  }
}

void bench_smt_setup2(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    SMTSubsumptionImpl smt_impl;
    bool smt_setup_result = smt_impl.setup2(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(smt_setup_result);
    benchmark::ClobberMemory();
  }
}




void bench_general_matching_no_bindings(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;

  for (auto _ : state) {
    int nmatches = 0;  // count matches to prevent optimization from removing code

    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit)) {
          nmatches += 1;
        }

        if (base_lit->commutative()) {
          ASS_EQ(base_lit->arity(), 2);
          ASS_EQ(inst_lit->arity(), 2);
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit)) {
            nmatches += 1;
          }
        }
      }
    }

    benchmark::DoNotOptimize(nmatches);
  }
}

void bench_general_matching_dhmap(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;
  MapBinderVampire binder;

  for (auto _ : state) {
    int nmatches = 0;  // count matches to prevent optimization from removing code
    int nbindings = 0;

    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          nmatches += 1;
          nbindings += binder.size();
        }

        if (base_lit->commutative()) {
          ASS_EQ(base_lit->arity(), 2);
          ASS_EQ(inst_lit->arity(), 2);
          binder.reset();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            nmatches += 1;
            nbindings += binder.size();
          }
        }
      }
    }

    benchmark::DoNotOptimize(nmatches);
    benchmark::DoNotOptimize(nbindings);
  }
}

void bench_general_matching_stl(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;
  MapBinderSTL binder;

  for (auto _ : state) {
    int nmatches = 0;  // count matches to prevent optimization from removing code
    int nbindings = 0;

    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          nmatches += 1;
          nbindings += binder.size();
        }

        if (base_lit->commutative()) {
          ASS_EQ(base_lit->arity(), 2);
          ASS_EQ(inst_lit->arity(), 2);
          binder.reset();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            nmatches += 1;
            nbindings += binder.size();
          }
        }
      }
    }

    benchmark::DoNotOptimize(nmatches);
    benchmark::DoNotOptimize(nbindings);
  }
}

class MapBinderArray1
{
  CLASS_NAME(MapBinderArray1);
  USE_ALLOCATOR(MapBinderArray1);

public:
  using Var = unsigned int;

  MapBinderArray1()
    : m_bindings(16)
  { }

  bool bind(Var var, TermList term)
  {
    size_t pos = m_var2pos.get(var);
    TermList& entry = m_bindings[pos];
    if (entry.isEmpty()) {
      ASS(term.isNonEmpty());
      entry = term;
      return true;
    } else {
      return entry == term;
    }
  }

  void specVar(unsigned var, TermList term)
  {
    ASSERTION_VIOLATION;
  }

  void initForBaseLiteral(Literal* baseLit)
  {
    static BinaryHeap<uint32_t, Int> varNums;
    varNums.reset();

    // Build ordered set of variables
    VariableIterator bvit(baseLit);
    while (bvit.hasNext()) {
      unsigned var = bvit.next().var();
      varNums.insert(var);
    }

    // Store variable positions in map
    m_var2pos.reset();
    unsigned nextPos = 0;
    while (!varNums.isEmpty()) {
      unsigned var = varNums.pop();
      while (!varNums.isEmpty() && varNums.top() == var) {
        varNums.pop();
      }
      if (m_var2pos.insert(var, nextPos)) {
        nextPos++;
      } else {
        ASSERTION_VIOLATION; // we remove all same variables above so how can this happen.
      }
    }
    unsigned numVars = nextPos;
    ASS_EQ(m_var2pos.size(), numVars);
  }

  void reset()
  {
    // TODO: could speed up reset using the timestamp-trick, at the cost of making the lookup slower
    TermList tl_empty;
    tl_empty.makeEmpty();
    m_bindings.init(m_var2pos.size(), tl_empty);
  }

  size_t size() const
  {
    return m_bindings.size();
  }

private:
  static_assert(std::is_same<unsigned, uint32_t>::value, "need unsigned==uint32_t");
  DHMap<uint32_t, uint32_t> m_var2pos;
  DArray<TermList> m_bindings;
};


void bench_general_matching_array1(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;
  MapBinderArray1 binder;

  for (auto _ : state) {
    int nmatches = 0;  // count matches to prevent optimization from removing code
    int nbindings = 0;

    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];
      binder.initForBaseLiteral(base_lit);

      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          nmatches += 1;
          nbindings += binder.size();
        }

        if (base_lit->commutative()) {
          ASS_EQ(base_lit->arity(), 2);
          ASS_EQ(inst_lit->arity(), 2);
          binder.reset();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            nmatches += 1;
            nbindings += binder.size();
          }
        }
      }
    }

    benchmark::DoNotOptimize(nmatches);
    benchmark::DoNotOptimize(nbindings);
  }
}

// general matching benchmark with ArrayStoringBinder2 (using linear search over pair<var,term> array)
class MapBinderArray2
{
  CLASS_NAME(MapBinderArray2);
  USE_ALLOCATOR(MapBinderArray2);

public:
  using Var = unsigned int;

  MapBinderArray2()
    : m_bindings(16)
  { }

  bool bind(Var var, TermList term)
  {
    for (std::pair<Var, TermList> entry : m_bindings) {
      if (entry.first == var) {
        return entry.second == term;
      }
    }
    m_bindings.push_back({var, term});
    return true;
  }

  void specVar(unsigned var, TermList term)
  {
    ASSERTION_VIOLATION;
  }

  void reset()
  {
    m_bindings.clear();
  }

  void sort()
  {
    std::sort(m_bindings.begin(), m_bindings.end());
  }

  size_t size() const
  {
    return m_bindings.size();
  }

public:  // this is just for benchmarking anyways
  vvector<std::pair<Var, TermList>> m_bindings;
};


void bench_general_matching_array2(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;
  MapBinderArray2 binder;

  for (auto _ : state) {
    int nmatches = 0;  // count matches to prevent optimization from removing code
    int nbindings = 0;

    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          nmatches += 1;
          nbindings += binder.size();
          // binder.sort();
          // if (binder.size() > 0) {
          //   benchmark::DoNotOptimize(binder.m_bindings.front());
          // }
        }

        if (base_lit->commutative()) {
          ASS_EQ(base_lit->arity(), 2);
          ASS_EQ(inst_lit->arity(), 2);
          binder.reset();
          if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
            nmatches += 1;
            nbindings += binder.size();
            // binder.sort();
            // if (binder.size() > 0) {
            //   benchmark::DoNotOptimize(binder.m_bindings.front());
            // }
          }
        }
      }
    }

    benchmark::DoNotOptimize(nmatches);
    benchmark::DoNotOptimize(nbindings);
  }
}



void bench_smt_matching(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;

  for (auto _ : state) {

    vvector<vvector<Alt>> alts;
    alts.reserve(side_premise->length());

    // for each instance literal (of main_premise),
    // the possible variables indicating a match with the instance literal
    vvector<vvector<Minisat::Var>> possible_base_vars;
    // start with empty vector for each instance literal
    possible_base_vars.resize(main_premise->length());

    MapBinder binder;

    // Matching for subsumption checks whether
    //
    //      side_premise\theta \subseteq main_premise
    //
    // holds.
    Minisat::Var nextVar = 0;
    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      vvector<Alt> base_lit_alts;
      base_lit_alts.reserve(2*main_premise->length());

      // TODO: use LiteralMiniIndex here (need to extend InstanceIterator to a version that returns the binder)
      // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          Minisat::Var b = nextVar++;

          if (binder.bindings().size() > 0) {
            ASS(!base_lit->ground());
            benchmark::DoNotOptimize(binder.bindings());
            benchmark::DoNotOptimize(binder.bindings().size());
          }
          else {
            ASS(base_lit->ground());
            ASS_EQ(base_lit, inst_lit);
            // TODO: in this case, at least for subsumption, we should skip this base_lit and this inst_list.
            // probably best to have a separate loop first that deals with ground literals? since those are only pointer equality checks.
            //
            // For now, just register an empty substitution atom.
            benchmark::DoNotOptimize(binder.bindings());
            benchmark::DoNotOptimize(binder.bindings().size());
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
            Minisat::Var b = nextVar++;

            benchmark::DoNotOptimize(binder.bindings());
            benchmark::DoNotOptimize(binder.bindings().size());

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
        state.SkipWithError("hmm, in this case it should not take that long");
      }
      alts.push_back(std::move(base_lit_alts));
    }

    benchmark::DoNotOptimize(alts.data());
    benchmark::DoNotOptimize(possible_base_vars.data());
    benchmark::ClobberMemory();
  }
}


// Optimization notes:
// Initial version: ~15000 ns
// Removing SubstitutionAtom::from_binder and stc.register_atom calls: ~10000ns
//
// Changelog:
void bench_smt_matching_with_stc(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;

  for (auto _ : state) {

    vvector<vvector<Alt>> alts;
    alts.reserve(side_premise->length());

    // for each instance literal (of main_premise),
    // the possible variables indicating a match with the instance literal
    vvector<vvector<Minisat::Var>> possible_base_vars;
    // start with empty vector for each instance literal
    possible_base_vars.resize(main_premise->length());

    SubstitutionTheoryConfiguration stc;
    MapBinder binder;

    // Matching for subsumption checks whether
    //
    //      side_premise\theta \subseteq main_premise
    //
    // holds.
    Minisat::Var nextVar = 0;
    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      vvector<Alt> base_lit_alts;
      base_lit_alts.reserve(2*main_premise->length());

      // TODO: use LiteralMiniIndex here (need to extend InstanceIterator to a version that returns the binder)
      // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          Minisat::Var b = nextVar++;

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
            Minisat::Var b = nextVar++;

            auto atom = SubstitutionAtom::from_binder(binder);
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
        state.SkipWithError("hmm, in this case it should not take that long");
      }
      alts.push_back(std::move(base_lit_alts));
    }

    benchmark::DoNotOptimize(alts.data());
    benchmark::DoNotOptimize(possible_base_vars.data());
    benchmark::DoNotOptimize(stc.get_atoms().data());
    benchmark::ClobberMemory();

  }
}



// Lines with !!! are new compared to previous test
void bench_smt_until_create_solver(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;

  for (auto _ : state) {

    vvector<vvector<Alt>> alts;
    alts.reserve(side_premise->length());

    // for each instance literal (of main_premise),
    // the possible variables indicating a match with the instance literal
    vvector<vvector<Minisat::Var>> possible_base_vars;
    // start with empty vector for each instance literal
    possible_base_vars.resize(main_premise->length());

    SubstitutionTheoryConfiguration stc;
    MapBinder binder;

    // Matching for subsumption checks whether
    //
    //      side_premise\theta \subseteq main_premise
    //
    // holds.
    Minisat::Var nextVar = 0;
    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      vvector<Alt> base_lit_alts;
      base_lit_alts.reserve(2*main_premise->length());

      // TODO: use LiteralMiniIndex here (need to extend InstanceIterator to a version that returns the binder)
      // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          Minisat::Var b = nextVar++;

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
            Minisat::Var b = nextVar++;

            auto atom = SubstitutionAtom::from_binder(binder);
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
        state.SkipWithError("hmm, in this case it should not take that long");
      }
      alts.push_back(std::move(base_lit_alts));
    }

    Minisat::Solver solver;                       // !!!
    benchmark::DoNotOptimize(solver);
    benchmark::DoNotOptimize(alts.data());
    benchmark::DoNotOptimize(possible_base_vars.data());
    benchmark::DoNotOptimize(stc.get_atoms().data());
    benchmark::ClobberMemory();
  }
}



// Lines with !!! are new compared to previous test
void bench_smt_until_create_theory(benchmark::State& state, SubsumptionInstance instance)
{
  Clause* side_premise = instance.side_premise;
  Clause* main_premise = instance.main_premise;

  for (auto _ : state) {

    vvector<vvector<Alt>> alts;
    alts.reserve(side_premise->length());

    // for each instance literal (of main_premise),
    // the possible variables indicating a match with the instance literal
    vvector<vvector<Minisat::Var>> possible_base_vars;
    // start with empty vector for each instance literal
    possible_base_vars.resize(main_premise->length());

    SubstitutionTheoryConfiguration stc;
    MapBinder binder;

    // Matching for subsumption checks whether
    //
    //      side_premise\theta \subseteq main_premise
    //
    // holds.
    Minisat::Var nextVar = 0;
    for (unsigned i = 0; i < side_premise->length(); ++i) {
      Literal* base_lit = side_premise->literals()[i];

      vvector<Alt> base_lit_alts;
      base_lit_alts.reserve(2*main_premise->length());

      // TODO: use LiteralMiniIndex here (need to extend InstanceIterator to a version that returns the binder)
      // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
      for (unsigned j = 0; j < main_premise->length(); ++j) {
        Literal* inst_lit = main_premise->literals()[j];

        if (!Literal::headersMatch(base_lit, inst_lit, false)) {
          continue;
        }

        binder.reset();
        if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
          Minisat::Var b = nextVar++;

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
            Minisat::Var b = nextVar++;

            auto atom = SubstitutionAtom::from_binder(binder);
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
        state.SkipWithError("hmm, in this case it should not take that long");
      }
      alts.push_back(std::move(base_lit_alts));
    }

    Minisat::Solver solver;
    solver.newVars(nextVar);                          // !!!
    solver.setSubstitutionTheory(std::move(stc));     // !!!

    benchmark::DoNotOptimize(solver);
    benchmark::DoNotOptimize(alts.data());
    benchmark::DoNotOptimize(possible_base_vars.data());
    benchmark::DoNotOptimize(stc.get_atoms().data());
    benchmark::ClobberMemory();
  }
}






void bench_smt_search(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    state.PauseTiming();
    SMTSubsumptionImpl smt_impl;
    bool smt_setup_result = smt_impl.setup(instance.side_premise, instance.main_premise);
    state.ResumeTiming();
    benchmark::ClobberMemory();
    bool smt_result = smt_setup_result && smt_impl.solve();
    benchmark::DoNotOptimize(smt_result);
    if (smt_result != instance.subsumed) {
      state.SkipWithError("Wrong result!");
      return;
    }
  }
}

void bench_orig_total(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    OriginalSubsumption::Impl orig_impl;
    bool orig_result = orig_impl.checkSubsumption(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(orig_result);
    if (orig_result != instance.subsumed) {
      state.SkipWithError("Wrong result!");
      return;
    }
  }
}

void bench_orig_total_reusing(benchmark::State& state, SubsumptionInstance instance)
{
  OriginalSubsumption::Impl orig_impl;
  benchmark::ClobberMemory();
  for (auto _ : state) {
    bool orig_result = orig_impl.checkSubsumption(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(orig_result);
    if (orig_result != instance.subsumed) {
      state.SkipWithError("Wrong result!");
      return;
    }
  }
}

void bench_orig_setup(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    OriginalSubsumption::Impl orig_impl;
    bool orig_setup_result = orig_impl.setup(instance.side_premise, instance.main_premise);
    benchmark::DoNotOptimize(orig_setup_result);
    benchmark::ClobberMemory();
  }
}

void bench_orig_search(benchmark::State& state, SubsumptionInstance instance)
{
  for (auto _ : state) {
    state.PauseTiming();
    OriginalSubsumption::Impl orig_impl;
    bool orig_setup_result = orig_impl.setup(instance.side_premise, instance.main_premise);
    state.ResumeTiming();
    benchmark::ClobberMemory();
    bool orig_result = orig_setup_result && orig_impl.solve();
    benchmark::DoNotOptimize(orig_result);
    if (orig_result != instance.subsumed) {
      state.SkipWithError("Wrong result!");
      return;
    }
  }
}

#endif


void ProofOfConcept::benchmark_micro(vvector<SubsumptionInstance> instances)
{
  CALL("ProofOfConcept::benchmark_micro");
  BYPASSING_ALLOCATOR;  // google-benchmark needs its own memory

  std::cerr << "\% SMTSubsumption: micro-benchmarking " << instances.size() << " instances" << std::endl;
#if VDEBUG
  std::cerr << "\n\n\nWARNING: compiled in debug mode!\n\n\n" << std::endl;
#endif

#if ENABLE_BENCHMARK

  vvector<char const*> args = {
    "vampire-sbench-micro",
    // "--benchmark_repetitions=10",  // Enable this to get mean/median/stddev
    // // "--benchmark_report_aggregates_only=true",
    // "--benchmark_display_aggregates_only=true",
    // // "--help",
  };
  char** argv = const_cast<char**>(args.data());  // not really legal but whatever
  int argc = args.size();

  // for (auto instance : instances)
  // for (int i = 0; i < 5; ++i)
  // for (int i = 0; i < instances.size(); ++i)
  for (int i = 0; i < 1; ++i)
  {
    auto instance = instances[i];
    std::string name;
    std::string suffix =
        std::to_string(instance.number); // + (instance.subsumed ? "_success" : "_failure");

    name = "general_matching_no_bindings_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_general_matching_no_bindings, instance);
    name = "general_matching_dhmap_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_general_matching_dhmap, instance);
    name = "general_matching_stl_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_general_matching_stl, instance);
    name = "general_matching_array1_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_general_matching_array1, instance);
    name = "general_matching_array2_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_general_matching_array2, instance);

    name = "smt_matching_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_matching, instance);
    name = "smt_matching_with_stc_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_matching_with_stc, instance);
    name = "smt_until_create_solver_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_until_create_solver, instance);
    name = "smt_until_create_theory_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_until_create_theory, instance);
    name = "smt_setup_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_setup, instance);
    name = "smt_setup2_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_setup2, instance);
    // break;
    name = "smt_search_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_search, instance);
    name = "smt_total_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_smt_total, instance);

    name = "orig_setup_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_orig_setup, instance);
    name = "orig_search_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_orig_search, instance);
    name = "orig_total_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_orig_total, instance);
    name = "orig_total_reusing_" + suffix;
    benchmark::RegisterBenchmark(name.c_str(), bench_orig_total_reusing, instance);
  }

  benchmark::Initialize(&argc, argv);
  benchmark::RunSpecifiedBenchmarks();
#endif

  std::cerr << "Benchmarking done, shutting down..." << std::endl;
}

/*
template <typename Duration>
vstring fmt_microsecs(Duration d) {
  std::uint64_t microsecs = std::chrono::duration_cast<std::chrono::microseconds>(d).count();
  vstringstream s;
  s << std::setw(10) << microsecs << " [µs]";
  return s.str();
}

template <typename Duration>
vstring fmt_nanosecs(Duration d) {
  std::uint64_t nanosecs = std::chrono::duration_cast<std::chrono::nanoseconds>(d).count();
  vstringstream s;
  s << std::setw(10) << nanosecs << " [ns]";
  return s.str();
}

void ProofOfConcept::benchmark_micro1(SubsumptionInstance instance)
{
  CALL("ProofOfConcept::benchmark_micro1");
  // TODO return results

  clobber();

  // TODO: this includes all allocation overhead, which is not what we want
  using namespace std::chrono;
  steady_clock::time_point smt_ts_begin = steady_clock::now();
  clobber();
  // uint64_t c1 = rdtscp();
  SMTSubsumptionImpl smt_impl;
  bool smt_result = smt_impl.checkSubsumption(instance.side_premise, instance.main_premise);
  // uint64_t c2 = rdtscp();
  clobber();
  steady_clock::time_point smt_ts_end = steady_clock::now();
  steady_clock::duration smt_duration = smt_ts_end - smt_ts_begin;

  clobber();

  steady_clock::time_point orig_ts_begin = steady_clock::now();
  clobber();
  OriginalSubsumption::Impl orig_impl;
  // uint64_t c1 = rdtscp();
  bool orig_result = orig_impl.checkSubsumption(instance.side_premise, instance.main_premise);
  // uint64_t c2 = rdtscp();
  clobber();
  steady_clock::time_point orig_ts_end = steady_clock::now();
  steady_clock::duration orig_duration = orig_ts_end - orig_ts_begin;

  clobber();


  std::cout << "Instance #" << instance.number << ": ";
  std::cout << "SMTS: " << fmt_nanosecs(smt_duration) << " / ";
  std::cout << "Orig: " << fmt_nanosecs(orig_duration);
  if (smt_duration < orig_duration) {
    std::cout << "  !!!!!!";
  }
  std::cout << std::endl;
  // std::cout << "SMT Subsumption: rdtscp: " << c2 - c1 << std::endl;

  if (smt_result != instance.subsumed) {
    std::cout << "ERROR: wrong result!" << std::endl;
  }
}
*/


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
