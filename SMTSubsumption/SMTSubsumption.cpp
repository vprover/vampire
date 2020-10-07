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
  std::cerr << "Side premise: " << side_premise->toString() << std::endl;
  std::cerr << "Main premise: " << main_premise->toString() << std::endl;

  Minisat::Solver solver;
  solver.verbosity = 2;
  // std::cout << "first var: " << solver.newVar() << std::endl;


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

      if (base_lit->arity() == 0 || MatchingUtils::matchArgs(base_lit, inst_lit, binder)) {
        if (!base_lit_alts.empty()) {
          std::cerr << " | ";
        }
        std::cerr << std::left << std::setw(20) << inst_lit->toString();

        // TODO: from binder, create the substitution theory literals
        // WE DO NOT need separate var for boolean skeleton, attach directly to "b"
        auto atom = SubstitutionAtom::from_binder(binder);
        std::cerr << "atom: " << atom << std::endl;

        Minisat::Var b = solver.newVar();
        stc.register_atom(b, std::move(atom));
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

          // TODO: from binder, create the substitution theory literals
          // ASSERTION_VIOLATION;  // TODO can't continue until we implement this properly
        auto atom = SubstitutionAtom::from_binder(binder);
        std::cerr << "atom: " << atom << std::endl;

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

  // SubstitutionTheory st{std::move(stc)};
  solver.setSubstitutionTheory(std::move(stc));

  // Pre-matching done
  for (auto const& v : alts) {
    if (v.empty()) {
      std::cerr << "There is a base literal without any possible matches => abort" << std::endl;
      return;
    }
  }

  // Add constraints:
  // \Land_i ExactlyOneOf(b_{i1}, ..., b_{ij})
  using Minisat::Lit;
  for (auto const& v : alts) {
    std::cerr << "blah" << std::endl;
    // At least one must be true
    Minisat::vec<Lit> cl;
    for (auto const& alt : v) {
      cl.push(Lit(alt.b));
    }
    std::cerr << "blah2" << std::endl;
    solver.addClause(cl);
    std::cerr << "blah3" << std::endl;
    // At most one must be true
    for (size_t j1 = 0; j1 < v.size(); ++j1) {
      for (size_t j2 = j1 + 1; j2 < v.size(); ++j2) {
        auto b1 = v[j1].b;
        auto b2 = v[j2].b;
        ASS_NEQ(b1, b2);
        using Minisat::Lit;
        solver.addBinary(~Lit(b1), ~Lit(b2));
      }
    }
    // for (auto const& alt1 : v) {
    //   for (auto const& alt2 : v) {
    //     if (alt1.b != alt2.b) {
    //       solver.addBinary(Minisat::Lit(alt1.b, true), Minisat::Lit(alt2.b, true));
    //     }
    //   }
    // }
  }

  // Add constraints:
  // \Land_j AtMostOneOf(b_{1j}, ..., b_{ij})
  for (auto const& w : possible_base_vars) {
    std::cerr << "blah4" << std::endl;
    for (size_t i1 = 0; i1 < w.size(); ++i1) {
      for (size_t i2 = i1 + 1; i2 < w.size(); ++i2) {
        auto b1 = w[i1];
        auto b2 = w[i2];
        ASS_NEQ(b1, b2);
        using Minisat::Lit;
        solver.addBinary(~Lit(b1), ~Lit(b2));
      }
    }
  }





  std::cerr << "gogogo" << std::endl;
  Minisat::Var x = solver.newVar();
  Minisat::Var y = solver.newVar();
  std::cout << "x-index: " << x << std::endl;
  std::cout << "y-index: " << y << std::endl;
  // solver.addBinary(Minisat::Lit{x,true},  Minisat::Lit{y,true});
  // solver.addBinary(Minisat::Lit{x,false}, Minisat::Lit{y,true});
  // solver.addBinary(Minisat::Lit{x,true},  Minisat::Lit{y,false});
  // solver.addBinary(Minisat::Lit{x,false}, Minisat::Lit{y,false});
  std::cerr << "solving" << std::endl;
  bool res = solver.solve({});
  std::cout << "Result: " << res << std::endl;


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
