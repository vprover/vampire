/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
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
: _cnt(cnt), _modified(true), _components(8)
{
  CALL("IntUnionFind::IntUnionFind");
  ASS_G(cnt, 0);

  _parents=reinterpret_cast<int*>(ALLOC_KNOWN(_cnt*sizeof(int), "IntUnionFind"));
  for(int i=0;i<_cnt;i++) {
    _parents[i]=-1;
  }
  _data=reinterpret_cast<int*>(ALLOC_KNOWN(_cnt*sizeof(int), "IntUnionFind"));
}

IntUnionFind::~IntUnionFind()
{
  DEALLOC_KNOWN(_parents, _cnt*sizeof(int), "IntUnionFind");
  DEALLOC_KNOWN(_data, _cnt*sizeof(int), "IntUnionFind");
}


void IntUnionFind::reset()
{
  CALL("IntUnionFind::reset");

  for(int i=0;i<_cnt;i++) {
    _parents[i]=-1;
  }
  _modified = true;
}


/**
 * Make sure c1 and c2 are in the same class. If c1 and c2 already
 * were in the same class, return false, otherwise return true.
 */
bool IntUnionFind::doUnion(int c1, int c2)
{
  CALL("IntUnionFind::doUnion");

  c1=root(c1);
  c2=root(c2);
  if(c1==c2) {
    return false;
  }
  if(c1>c2) {
    swap(c1,c2);
  }
  ASS_EQ(_parents[c2],-1);
  _parents[c2]=c1;

  //the component structure has changed
  _modified=true;
  return true;
}

/**
 * Get a root of a element, if two elements have the same root,
 * they are in one component.
 */
int IntUnionFind::root(int c) const
{
  CALL("IntUnionFind::root");

  static Stack<int> path(8);
  ASS(path.isEmpty());
  int prev=-1;

  while(_parents[c]!=-1) {
    if(prev!=-1) {
      path.push(prev);
    }
    prev=c;
    c=_parents[c];
  }

  while(path.isNonEmpty()) {
    _parents[path.pop()]=c;
  }
  return c;
}

void IntUnionFind::evalComponents()
{
  CALL("IntUnionFind::evalComponents");

  if(!_modified) {
    //the components are already evaluated
    return;
  }

  _components.reset();

  for(int i=0;i<_cnt;i++) {
    _data[i]=_parents[i];
  }
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
  ASS_G(_components.size(),0);
  _modified=false;
}

/**
 * Return the number of components
 *
 * The @b evalComponents function must be called before
 * this function is called (and if the @b doUnion is called
 * later, the @b evalComponents has to be called again).
 */
int IntUnionFind::getComponentCount()
{
  CALL("IntUnionFind::getComponentCount");
  ASS(!_modified);

  return _components.size();
}


}
