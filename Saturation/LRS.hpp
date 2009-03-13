/**
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "../Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

//TODO: implement!!!

class LRS
: public SaturationAlgorithm
{
public:
  LRS(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
    : SaturationAlgorithm(passiveContainer,selector) {}
  SaturationResult saturate();

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

protected:
  bool processUnprocessed(Clause* c);
  void backwardSimplify(Clause* c);
  void activate(Clause* c);

  long getReachableCountEstimate();

  struct FakeContainer
  : public ClauseContainer
  {
    void add(Clause* c)
    { addedEvent.fire(c); }

    void remove(Clause* c)
    { removedEvent.fire(c); }
  };

  FakeContainer _simplCont;
};

};

#endif /* __LRS__ */
