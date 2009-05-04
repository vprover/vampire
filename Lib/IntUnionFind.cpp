/**
 * @file IntUnionFind.cpp
 * Implements class IntUnionFind with union-find algorithm for integers.
 */

#include <algorithm>

#include "Allocator.hpp"

#include "IntUnionFind.hpp"

namespace Lib {

using namespace std;

IntUnionFind::IntUnionFind(int cnt)
: _cnt(cnt), _components(8)
{
  CALL("IntUnionFind::IntUnionFind");

  _data=reinterpret_cast<int*>(ALLOC_KNOWN(_cnt*sizeof(int), "IntUnionFind"));
  for(int i=0;i<_cnt;i++) {
    _data[i]=-1;
  }
}

IntUnionFind::~IntUnionFind()
{
  DEALLOC_KNOWN(_data, _cnt*sizeof(int), "IntUnionFind");
}

void IntUnionFind::doUnion(int c1, int c2)
{
  CALL("IntUnionFind::doUnion");

  c1=root(c1);
  c2=root(c2);
  if(c1==c2) {
    return;
  }
  if(c1>c2) {
    swap(c1,c2);
  }
  ASS_EQ(_data[c2],-1);
  _data[c2]=c1;
}

int IntUnionFind::root(int c)
{
  CALL("IntUnionFind::root");

  static Stack<int> path(8);
  ASS(path.isEmpty());
  int prev=-1;

  while(_data[c]!=-1) {
    if(prev!=-1) {
      path.push(prev);
    }
    prev=c;
    c=_data[c];
  }

  while(path.isNonEmpty()) {
    _data[path.pop()]=c;
  }
  return c;
}

void IntUnionFind::finish()
{
  CALL("IntUnionFind::finish");
  ASS(_components.isEmpty());

  for(int i=0;i<_cnt;i++) {
    if(_data[i]==-1) {
      _components.push(i);
    } else {
      int prev=_data[i];
      ASS_L(prev,i);
      _data[i]=_data[prev];
      _data[prev]=i;
    }
  }
}



}
