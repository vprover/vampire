#include "SMTSubsumption.hpp"
#include "SMTSubsumption/minisat/Solver.h"

using namespace Kernel;
using namespace SMTSubsumption;


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
  std::cout << "Result: " << res << std::endl;
}
