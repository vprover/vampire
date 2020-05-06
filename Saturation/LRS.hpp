
/*
 * File LRS.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "Forwards.hpp"

#include "Lib/Event.hpp"

#include "Otter.hpp"

namespace Saturation {

using namespace Kernel;

class LRS
: public Otter
{
public:
  CLASS_NAME(LRS);
  USE_ALLOCATOR(LRS);

  LRS(Problem& prb, const Options& opt)
  : Otter(prb, opt), _limitsEverActive(false) {}

  virtual ~LRS() {}

protected:

  //overrides SaturationAlgorithm::isComplete
  bool isComplete();

  //overrides SaturationAlgorithm::onUnprocessedSelected
  void onUnprocessedSelected(Clause* c);

  bool shouldUpdateLimits();

  long long estimatedReachableCount();

  bool _limitsEverActive;
};

};

#endif /* __LRS__ */
