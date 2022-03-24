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

#include "Lib/ArrayMap.hpp"
#include "Lib/DynamicHeap.hpp"
#include "Lib/Int.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;



TEST_FUN(dheapFewElements)
{
  DynamicHeap<int, Int> dh;
  
  int cnt=10;
  int primeAfterCnt=13;
  for(int i=0;i<cnt;i++)
  {
    dh.insert((i*10)%primeAfterCnt);
  }
  
  
  int prev=0;
  while(!dh.isEmpty()) {
    int cur=dh.pop();
    ASS(cur>=prev);
    prev=cur;
  }
}

TEST_FUN(dheapMoreElements)
{
  DynamicHeap<int, Int> dh;

  int cnt=100;
  int primeAfterCnt=113;

  for(int i=1;i<cnt;i++)
  {
    int num=(i*10)%primeAfterCnt;
    dh.insert(num);
    dh.insert(-num);
  }

  int resCnt=0;
  int prev=INT_MIN;
  while(!dh.isEmpty()) {
    int cur=dh.pop();
    ASS_G(cur,prev);
    prev=cur;
    resCnt++;
  }
  ASS_EQ(resCnt,2*(cnt-1));
}

struct IndirectComparator
{
  IndirectComparator(int* vals) : _vals(vals) {}
  Comparison compare(unsigned a, unsigned b)
  {
    return Int::compare(_vals[a], _vals[b]);
  }
  int* _vals;
};

TEST_FUN(dheapDecreasing)
{
  int cnt=100;
  int vals[100];

  IndirectComparator myCmp(vals);
  DynamicHeap<int, IndirectComparator> dh(myCmp);

  for(int i=0;i<cnt;i++) {
    int idx = (i*3)%100;
    vals[idx] = idx;
    dh.insert(idx);
  }

  for(int i=0;i<cnt;i++) {
    int idx = (i*7)%100;
    vals[idx] = -idx;
    dh.notifyDecrease(idx);
  }

  int resCnt=0;
  int prev=INT_MIN;
  while(!dh.isEmpty()) {
    int cur=dh.pop();
    if(prev!=INT_MIN) {
      ASS_G(vals[cur],vals[prev]);
    }
    prev=cur;
    resCnt++;
  }
  ASS_EQ(resCnt,cnt);
}

TEST_FUN(dheapIncreasing)
{
  int cnt=100;
  int vals[100];

  IndirectComparator myCmp(vals);
  DynamicHeap<int, IndirectComparator, ArrayMap<unsigned> > dh(myCmp);
  dh.elMap().expand(cnt);

  for(int i=0;i<cnt;i++) {
    int idx = (i*3)%100;
    vals[idx] = idx;
    dh.insert(idx);
  }

  for(int i=0;i<cnt;i++) {
    int idx = (i*7)%100;
    vals[idx] = idx+1000;
    dh.notifyIncrease(idx);
  }

  int resCnt=0;
  int prev=INT_MIN;
  while(!dh.isEmpty()) {
    ASS(dh.contains(resCnt));
    int cur=dh.pop();
    ASS(!dh.contains(resCnt));
    ASS_EQ(cur, resCnt);
    if(prev!=INT_MIN) {
      ASS_G(vals[cur],vals[prev]);
    }
    prev=cur;
    resCnt++;
  }
  ASS_EQ(resCnt,cnt);
}
