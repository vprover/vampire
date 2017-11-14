
/*
 * File tBinaryHeap.cpp.
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

#include "Lib/BinaryHeap.hpp"
#include "Lib/Int.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID bheap
UT_CREATE;

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
