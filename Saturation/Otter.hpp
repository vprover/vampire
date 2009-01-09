/**
 * @file Otter.hpp
 * Defines class Otter.
 */


#ifndef __Otter__
#define __Otter__

#include "../Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class Otter
: public SaturationAlgorithm
{
public:
  Otter(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
    : SaturationAlgorithm(passiveContainer,selector) {}
  SaturationResult saturate();

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

protected:
  bool processUnprocessed(Clause* c);
  void backwardSimplify(Clause* c);
  void activate(Clause* c);

  class FakeContainer
  : public ClauseContainer
  {
  public:
    void add(Clause* c)
    { addedEvent.fire(c); }

    void remove(Clause* c)
    { removedEvent.fire(c); }
  };

  FakeContainer _simplCont;
};

};

#endif /* __Otter__ */
