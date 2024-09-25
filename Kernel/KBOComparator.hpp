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
 * @file KBOComparator.hpp
 * Defines comparator class for KBO.
 */

#ifndef __KBOComparator__
#define __KBOComparator__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

#include "OrderingComparator.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Runtime specialized KBO ordering check, based on the linear KBO check
 * also implemented in @b KBO.
 */
class KBOComparator
: public OrderingComparator
{
public:
  KBOComparator(const Ordering& ord, const Stack<Ordering::Constraint>& comps, void* result)
    : OrderingComparator(ord, comps, result) {}

  void expandTermCase(ComparisonNode* node) override;
};

}
#endif
