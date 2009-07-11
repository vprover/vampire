/**
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class LRS
: public SaturationAlgorithm
{
public:
  LRS(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector);

  SaturationResult saturate();

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

protected:
  bool shouldUpdateLimits();

  long estimatedReachableCount();

  void addInputSOSClause(Clause* cl);

  void onActiveRemoved(Clause* cl);
  void onPassiveRemoved(Clause* cl);


  /**
   * Dummy container for simplification indexes to subscribe
   * to its events.
   */
  struct FakeContainer
  : public ClauseContainer
  {
    /**
     * This method is called by @b saturate() method when a clause
     * makes it from unprocessed to passive container.
     */
    void add(Clause* c)
    { addedEvent.fire(c); }

    /**
     * This method is subscribed to remove events of passive
     * and active container, so it gets called automatically
     * when a clause is removed from one of them. (Clause
     * selection in passive container doesn't count as removal.)
     */
    void remove(Clause* c)
    { removedEvent.fire(c); }
  };


  FakeContainer _simplCont;
};

};

#endif /* __LRS__ */
