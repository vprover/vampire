/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include <iostream>
#include "Lib/List.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

TEST_FUN(list_1)
{
  IntList* lst = 0;

  IntList::push(0, lst);
  IntList::push(1, lst);

  IntList::DelIterator dit(lst);
  ALWAYS(dit.hasNext());
  ALWAYS(dit.next()==1);
  dit.del();
  ASS_EQ(lst->head(), 0);
  ASS_ALLOC_TYPE(lst, "List");
}
