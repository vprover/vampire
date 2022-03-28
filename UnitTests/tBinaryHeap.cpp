/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include <climits>

#include "Lib/BinaryHeap.hpp"
#include "Lib/Int.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;


TEST_FUN(bheap1)
{
  BinaryHeap<int, Int> bh;
  
  int cnt=10;
  for(int i=0;i<cnt;i++)
  {
    int num=rand()%cnt;
    bh.insert(num);
  }
  
  int prev=0;
  while(!bh.isEmpty()) {
    int cur=bh.pop();
    ASS(cur>=prev);
    prev=cur;
  }
}

TEST_FUN(bheap2)
{
  BinaryHeap<int, Int> bh;

  int cnt=100;

  for(int i=0;i<cnt;i++)
  {
    int num=rand()%cnt;
    bh.insert(num);
    bh.insert(-num);
  }

  int resCnt=0;
  int prev=INT_MIN;
  while(!bh.isEmpty()) {
    int cur=bh.pop();
    ASS(cur>=prev);
    prev=cur;
    resCnt++;
  }
  ASS_EQ(resCnt,200);
}
