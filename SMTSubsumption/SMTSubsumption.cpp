#include "SMTSubsumption.hpp"
#include "SMTSubsumption/minisat/Solver.h"
#include "Indexing/LiteralMiniIndex.hpp"
#include "Lib/STL.hpp"

#include <iostream>
#include <iomanip>

using namespace Indexing;
using namespace Kernel;
using namespace SMTSubsumption;



namespace {
  typedef DHMap<unsigned,TermList,IdentityHash> BindingMap;
  struct MapBinder
  {
    bool bind(unsigned var, TermList term)
    {
      TermList* aux;
      return _map.getValuePtr(var,aux,term) || *aux==term;
    }
    void specVar(unsigned var, TermList term)
    { ASSERTION_VIOLATION; }
    void reset() { _map.reset(); }
  private:
    BindingMap _map;
  };
}


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
  Minisat::Var x = solver.newVar();
  Minisat::Var y = solver.newVar();
  solver.addBinary(Minisat::Lit{x,true},  Minisat::Lit{y,true});
  solver.addBinary(Minisat::Lit{x,false}, Minisat::Lit{y,true});
  solver.addBinary(Minisat::Lit{x,true},  Minisat::Lit{y,false});
  // solver.addBinary(Minisat::Lit{x,false}, Minisat::Lit{y,false});
  bool res = solver.solve({});
  std::cout << "x-index: " << x << std::endl;
  std::cout << "y-index: " << y << std::endl;
  std::cout << "Result: " << res << std::endl;


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

        base_lit_alts.push_back({
          .lit = inst_lit,
          .j = j,
          .b = solver.newVar(),
          .reversed = false,
        });
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

          base_lit_alts.push_back({
            .lit = inst_lit,
            .j = j,
            .b = solver.newVar(),
            .reversed = true,
          });
        }
      }
    }

    std::cerr << std::endl;

    alts.push_back(std::move(base_lit_alts));
  }
}
