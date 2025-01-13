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
  Otter(Problem& prb, const Options& opt);

protected:

  void onSOSClauseAdded(Clause* cl) override;

  void onPassiveAdded(Clause* cl) override;

  void onPassiveRemoved(Clause* cl) override;

  void onClauseRetained(Clause* cl) override;



  /** called before the selected clause is deleted from the searchspace */
  void beforeSelectedRemoved(Clause* cl) override;
};

};

#endif /* __Otter__ */
