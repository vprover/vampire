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
#include "Debug/Assertion.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Int.hpp"
#include "Lib/SafeRecursion.hpp"
#include "Lib/Stack.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

typedef DArray<Stack<unsigned> > Tree;
Tree& getGraph()
{
  static bool init=false;
  static DArray<Stack<unsigned> > tree;
  if(!init) {
    init = true;
    tree.ensure(10);
    tree[0].push(1);
    tree[0].push(2);
    tree[0].push(3);
    tree[3].push(4);
    tree[3].push(5);
    tree[3].push(6);
    tree[3].push(7);
    tree[6].push(8);
    tree[6].push(9);
  }
  return tree;
}

struct SRWorkerBase
{
  template<class ChildCallback>
  void pre(unsigned obj, ChildCallback fn) {
    CALL("SRWorkerBase::pre");
    Stack<unsigned>& children = getGraph()[obj];
    Stack<unsigned>::BottomFirstIterator cit(children);
    while(cit.hasNext()) {
      unsigned c = cit.next();
      fn(c);
    }
  }
};

struct MaxDegreeRetrievalWorker : public SRWorkerBase
{
  int post(unsigned obj, size_t childCnt, int* childRes)
  {
    CALL("MaxDegreeRetrievalWorker::post");
    int res = childCnt;
    for(size_t i=0; i<childCnt; i++) {
      if(childRes[i]>res) {
	res = childRes[i];
      }
    }
    return res;
  }
};


TEST_FUN(safeRecMaxDeg)
{
  MaxDegreeRetrievalWorker wrk;

  unsigned res = SafeRecursion<unsigned,int,MaxDegreeRetrievalWorker>(wrk)(0);
  ASS_EQ(res,4);
}

struct StrRepWorker : public SRWorkerBase
{
  vstring post(unsigned obj, size_t childCnt, vstring* childRes)
  {
    CALL("MaxDegreeRetrievalWorker::post");
    vstring res = Int::toString(obj);
    if(childCnt==0) {
      return res;
    }
    res+="(";
    for(size_t i=0; i<childCnt; i++) {
      if(i!=0) {
	res+=",";
      }
      res+=childRes[i];
    }
    res+=")";
    return res;
  }
};

TEST_FUN(safeRecStrRep)
{
  StrRepWorker wrk;

  vstring res = SafeRecursion<unsigned,vstring,StrRepWorker>(wrk)(0);
  ASS_EQ(res,"0(1,2,3(4,5,6(8,9),7))");
}

