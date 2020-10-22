#include "SMTSubsumption.hpp"
#include "SubstitutionTheory.hpp"
#include "SMTSubsumption/minisat/Solver.h"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

#include <iostream>
#include <iomanip>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;



// namespace {
//   typedef DHMap<unsigned,TermList,IdentityHash> BindingMap;
//   struct MapBinder
//   {
//     bool bind(unsigned var, TermList term)
//     {
//       TermList* aux;
//       return _map.getValuePtr(var,aux,term) || *aux==term;
//     }
//     void specVar(unsigned var, TermList term)
//     { ASSERTION_VIOLATION; }
//     void reset() { _map.reset(); }
//   private:
//     BindingMap _map;
//   };
// }


/// Possible match alternative for a certain literal of the side premise.
struct Alt
{
  Literal* lit;  // the FOL literal
  unsigned j;    // index of lit in the main_premise
  Minisat::Var b;  // the b_{ij} representing this choice in the SAT solver
  bool reversed;
};

// /// Possible match alternatives for a certain literal of the side premise.
// struct Alts
// {
//   vvector<Literal*> alts;
// };


void ProofOfConcept::test(Clause* side_premise, Clause* main_premise)
{
  CALL("ProofOfConcept::test");

  std::cerr << "SMTSubsumption:\n";
  std::cerr << "Side premise (base):     " << side_premise->toString() << std::endl;
  std::cerr << "Main premise (instance): " << main_premise->toString() << std::endl;

  std::cerr << "alignof Solver : " << alignof(Minisat::Solver) << std::endl;
  std::cerr << "alignof Solver*: " << alignof(Minisat::Solver*) << std::endl;
  std::cerr << "alignof Clause : " << alignof(Minisat::Clause) << std::endl;
  std::cerr << "alignof Clause*: " << alignof(Minisat::Clause*) << std::endl;
  std::cerr << " sizeof Clause : " << sizeof(Minisat::Clause) << std::endl;
  std::cerr << " sizeof Clause*: " << sizeof(Minisat::Clause*) << std::endl;

  // Clause* base_cl = side_premise;
  // Clause* inst_cl = main_premise;

  Minisat::Solver solver;
  solver.verbosity = 2;

  // Matching for subsumption checks whether
  //
  //      side_premise\theta \subseteq main_premise
  //
  // holds.

  LiteralMiniIndex const main_premise_mini_index(main_premise);

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

  for (unsigned i = 0; i < side_premise->length(); ++i) {
    Literal* base_lit = side_premise->literals()[i];

    vvector<Alt> base_lit_alts;

    std::cerr
      << std::left << std::setw(20) << base_lit->toString()
      << " -> ";

    // TODO: use LiteralMiniIndex here (need to extend InstanceIterator to a version that returns the binder)
    // LiteralMiniIndex::InstanceIterator inst_it(main_premise_mini_index, base_lit, false);
    for (unsigned j = 0; j < main_premise->length(); ++j) {
      Literal* inst_lit = main_premise->literals()[j];

      if (!Literal::headersMatch(base_lit, inst_lit, false)) {
        continue;
      }

      MapBinder binder;

      binder.reset();
      if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
        Minisat::Var b = solver.newVar();

        if (!base_lit_alts.empty()) {
          std::cerr << " | ";
        }
        std::cerr << std::right << std::setw(20) << inst_lit->toString() << " [b_" << b << "]";

        if (binder.bindings().size() > 0) {
          ASS(!base_lit->ground());
          auto atom = SubstitutionAtom::from_binder(binder);
          // std::cerr << "atom: " << atom << std::endl;
          stc.register_atom(b, std::move(atom));
        } else {
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
          .lit = inst_lit,
          .j = j,
          .b = b,
          .reversed = false,
        });
        possible_base_vars[j].push_back(b);
      }

      if (base_lit->commutative()) {
        ASS_EQ(base_lit->arity(), 2);
        ASS_EQ(inst_lit->arity(), 2);
        binder.reset();
        if (MatchingUtils::matchReversedArgs(base_lit, inst_lit, binder)) {
          if (!base_lit_alts.empty()) {
            std::cerr << " | ";
          }
          std::cerr << "REV: " << std::left << std::setw(20) << inst_lit->toString();

          auto atom = SubstitutionAtom::from_binder(binder);
          // std::cerr << "atom: " << atom << std::endl;

          Minisat::Var b = solver.newVar();
          stc.register_atom(b, std::move(atom));

          // Minisat::Var b = solver.newVar();
          base_lit_alts.push_back({
            .lit = inst_lit,
            .j = j,
            .b = b,
            .reversed = true,
          });
          possible_base_vars[j].push_back(b);
        }
      }
    }

    std::cerr << std::endl;

    alts.push_back(std::move(base_lit_alts));
  }

  solver.setSubstitutionTheory(std::move(stc));

  // Pre-matching done
  for (auto const& v : alts) {
    if (v.empty()) {
      std::cerr << "There is a base literal without any possible matches => abort" << std::endl;
      return;
    }
  }

#define USE_ATMOSTONE_CONSTRAINTS 1

  // TODO: for these we can add special constraints to MiniSAT! see paper for idea
  // Add constraints:
  // \Land_i ExactlyOneOf(b_{i1}, ..., b_{ij})
  using Minisat::Lit;
  for (auto const& v : alts) {
    // At least one must be true
    Minisat::vec<Lit> ls;
    for (auto const& alt : v) {
      ls.push(Lit(alt.b));
    }
    solver.addClause(ls);
    // At most one must be true
#if USE_ATMOSTONE_CONSTRAINTS
    if (ls.size() >= 2) {
      solver.addConstraint_AtMostOne(ls);
    }
#else
    for (size_t j1 = 0; j1 < v.size(); ++j1) {
      for (size_t j2 = j1 + 1; j2 < v.size(); ++j2) {
        auto b1 = v[j1].b;
        auto b2 = v[j2].b;
        ASS_NEQ(b1, b2);
        solver.addBinary(~Lit(b1), ~Lit(b2));
      }
    }
#endif
  }

  // Add constraints:
  // \Land_j AtMostOneOf(b_{1j}, ..., b_{ij})
  for (auto const& w : possible_base_vars) {
#if USE_ATMOSTONE_CONSTRAINTS
    if (w.size() >= 2) {
      Minisat::vec<Lit> ls;
      for (auto const& b : w) {
        ls.push(Lit(b));
      }
      solver.addConstraint_AtMostOne(ls);
    }
#else
    for (size_t i1 = 0; i1 < w.size(); ++i1) {
      for (size_t i2 = i1 + 1; i2 < w.size(); ++i2) {
        auto b1 = w[i1];
        auto b2 = w[i2];
        ASS_NEQ(b1, b2);
        solver.addBinary(~Lit(b1), ~Lit(b2));
      }
    }
#endif
  }

  std::cout << "ok before solving? " << solver.okay() << std::endl;
  std::cerr << "solving" << std::endl;
  bool res = solver.solve({});
  std::cout << "Result: " << res << std::endl;
  std::cout << "ok: " << solver.okay() << std::endl;
}


// Example commutativity:
// side: f(x) = y
// main: f(d) = f(e)
// possible matchings:
// - x->d, y->f(e)
// - x->e, y->f(d)

// Example by Bernhard re. problematic subsumption demodulation:
// side: x1=x2 or x3=x4 or x5=x6 or x7=x8
// main: x9=x10 or x11=x12 or x13=14 or P(t)
