/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Otter.hpp
 * Defines class Otter.
 */


#ifndef __Otter__
#define __Otter__

#include "Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class Otter
: public SaturationAlgorithm
{
public:
  CLASS_NAME(Otter);
  USE_ALLOCATOR(Otter);

  Otter(Problem& prb, const Options& opt);

  ClauseContainer* getSimplifyingClauseContainer() override;

protected:

  void onSOSClauseAdded(Clause* cl) override;

  void onActiveRemoved(Clause* cl) override;

  void onPassiveAdded(Clause* cl) override;

  void onPassiveRemoved(Clause* cl) override;

  void onClauseRetained(Clause* cl) override;



  /** called before the selected clause is deleted from the searchspace */
  void beforeSelectedRemoved(Clause* cl) override;

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

#endif /* __Otter__ */
