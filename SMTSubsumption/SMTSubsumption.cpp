#include "SMTSubsumption.hpp"

using namespace Kernel;


void SMTSubsumption::test(Clause* side_premise, Clause* main_premise)
{
  CALL("SMTSubsumption::test");

  std::cerr << "SMTSubsumption:\n";
  std::cerr << "Side premise: " << side_premise->toString() << std::endl;
  std::cerr << "Main premise: " << main_premise->toString() << std::endl;

  // TODO
}
