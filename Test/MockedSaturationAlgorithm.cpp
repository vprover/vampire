#include "MockedSaturationAlgorithm.hpp"
#include "Kernel/Clause.hpp"

using namespace Kernel;

namespace Test {

void MockedSaturationAlgorithm::addPassive(Clause* cl)
{
  cl->setStore(Clause::PASSIVE);
  _passive->add(cl);
  // onPassiveAdded(cl);
}

void MockedSaturationAlgorithm::addActive(Clause* cl) 
{
  cl->setStore(Clause::ACTIVE);
  _active->add(cl);
  // onActiveAdded(cl);
}

} // namespace Test
