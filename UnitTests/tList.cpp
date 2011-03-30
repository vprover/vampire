#include <iostream>
#include "Lib/List.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID list
UT_CREATE;

using namespace std;
using namespace Lib;

typedef List<int> IntList;

TEST_FUN(list1)
{
  IntList* lst = 0;

  IntList::push(0, lst);
  IntList::push(1, lst);

  IntList::DelIterator dit(lst);
  ALWAYS(dit.hasNext());
  ALWAYS(dit.next()==0);
  dit.del();
  ASS_EQ(lst->head(), 1);
  ASS_ALLOC_TYPE(lst, "List");
}
