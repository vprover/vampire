/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;



TEST_FUN(stackDelIterator)
{
  Stack<unsigned> st1;

  int cnt=100; //must be even
  for(int i=0;i<cnt;i++) {
    st1.push(i);
  }
  
  {
    Stack<unsigned>::StableDelIterator dit1(st1);
    ALWAYS(dit1.hasNext());
    ALWAYS(dit1.next()==0);
    dit1.del();
    ALWAYS(dit1.hasNext());
    ALWAYS(dit1.next()==1);
  }

  ASS_EQ((int)st1.size(),cnt-1);
  
  {
    Stack<unsigned>::StableDelIterator dit2(st1);
    for(int i=1;i<cnt;i++) {
      ALWAYS(dit2.hasNext());
      ALWAYS((int)dit2.next()==i);
    }
    dit2.del();
  }
  ASS_EQ((int)st1.size(),cnt-2);
  ASS_EQ((int)st1.top(),cnt-2);
  st1.push(cnt-1);

  {
    Stack<unsigned>::StableDelIterator dit3(st1);
    while(dit3.hasNext()) {
      if(dit3.next()%2==0) {
	dit3.del();
      }
    }
  }
  ASS_EQ((int)st1.size(),cnt/2);
  {
    Stack<unsigned>::StableDelIterator dit4(st1);
    while(dit4.hasNext()) {
      ALWAYS(dit4.next()%2==1);
    }
  }
}
