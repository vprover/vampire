/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LPOComparator__
#define __LPOComparator__

#include "Forwards.hpp"

#include "OrderingComparator.hpp"

namespace Kernel {

using namespace Lib;
using namespace std;

class LPOComparator
: public OrderingComparator
{
public:
  LPOComparator(const Ordering& ord) : OrderingComparator(ord) {}

  void processTermNode() override;
};

}
#endif
