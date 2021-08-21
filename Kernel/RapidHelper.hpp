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
 * @file InductionHelper.hpp
 * Defines class InductionHelper
 *
 */

#ifndef __InductionHelper__
#define __InductionHelper__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

namespace Kernel {

using namespace Indexing;

class RapidHelper {
public:
  CLASS_NAME(RapidHelper);
  USE_ALLOCATOR(RapidHelper);

  RapidHelper() {}

  static bool isRightLimitLiteral(Literal* l);
  static bool isLeftLimitLiteral(Literal* l);  
  //if literal is a constant of the form Dense-x-l# for some variable x
  //and some time point l#
  static bool isDensityLiteral(Literal* l, unsigned& varFunctor, unsigned& tpFunctor);
  static bool isIntegerComparisonLiteral(Literal* l);

};

};  // namespace Kernel

#endif /*__InductionHelper__*/
