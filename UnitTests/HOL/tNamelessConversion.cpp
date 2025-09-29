/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/TypedTermList.hpp"
#include "Test/UnitTesting.hpp"

using namespace Kernel;

TEST_FUN(1) {
  TermList sort = TermList(AtomicSort::createConstant("sort"));

  TypedTermList x1 = TypedTermList(TermList::var(1), sort);
  //auto t = LAM(x1, AP(f, x1));
}