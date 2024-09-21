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
  KBOComparator(const Ordering& ord, TermList lhs, TermList rhs)
    : OrderingComparator(ord, lhs, rhs) {}

  /** Executes the runtime specialized instructions with concrete substitution. */
  bool check(const SubstApplicator* applicator) override;

  static void expand(const Ordering& ord, Branch& branch, const Stack<TermPairRes>& cache);
};

}
#endif
