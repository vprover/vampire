
/*
 * File tList.cpp.
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
#include <iostream>
#include "Lib/List.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID list
UT_CREATE;

using namespace std;
using namespace Lib;

TEST_FUN(list1)
{
  List<int>* lst = 0;

  List<int>::push(0, lst);
  List<int>::push(1, lst);

  List<int>::DelIterator dit(lst);
  ALWAYS(dit.hasNext());
  ALWAYS(dit.next()==1);
  dit.del();
  ASS_EQ(lst->head(), 0);
  ASS_ALLOC_TYPE(lst, "List");
}
