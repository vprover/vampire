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
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "Forwards.hpp"

#include "Otter.hpp"

namespace Saturation {

using namespace Kernel;

class LRS
: public Otter
{
public:
  using Otter::Otter;

protected:
  void poppedFromUnprocessed(Clause* c) override;

  bool shouldUpdateLimits();

  long long estimatedReachableCount();
};

};

#endif /* __LRS__ */
