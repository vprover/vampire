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
 * @file PredicateTypePromotion.hpp
 * A preprocessing step which lifts unary predicates to sorts in some cases
 */

#ifndef __PredicateTypePromotion__
#define __PredicateTypePromotion__

#include "Kernel/Problem.hpp"

namespace Shell {

class PredicateTypePromotion
{
public:
  void apply(Kernel::Problem &prb);
};

};

#endif /* __PredicateTypePromotion__ */
