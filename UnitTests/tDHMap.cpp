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

#include "Lib/DHMap.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

class IdHash {
public:
  static unsigned hash(unsigned i)
  {
    return i;
  }
};

class ConstHash {
public:
  static unsigned hash(unsigned i)
  {
    return 1;
  }
};

/**
 * Hash class for integers which iterates through
 * {0,1,...,capacity-1} in a zig-zag manner:
 * 
 * E.g. for capacity==3, the transformation is { 0->2,
 * 1->1, 2->0, 3->0, 4->1, 5->2, 6->2,... }
 */
class ZigZagHash {
public:
  /**
   * Hash function for integers which iterates through
   * {0,1,...,capacity-1} in a zig-zag manner:
   * 
   * E.g. for capacity==3, the transformation is { 0->2,
   * 1->1, 2->0, 3->0, 4->1, 5->2, 6->2,... }
   */
  static unsigned hash(unsigned i, int capacity)
  {
    int res=(i%(capacity*2) - capacity);
    if(res<0)
      //this turns x into -x-1
      res = ~res;
    return static_cast<unsigned>(res);
  }
};

namespace Lib 
{
/**
 * Traits structure specialisation. (See DHMap.hpp) 
 */
template<>
struct HashTraits<ZigZagHash>
{
  enum {SINGLE_PARAM_HASH=0};
};
};



typedef DHMap<unsigned, unsigned, ZigZagHash, ConstHash> MyMap;

TEST_FUN(dhmap1)
{
  MyMap m1;
  m1.insert(1,1);
  m1.insert(2,4);
  m1.insert(3,9);
  m1.insert(5,25);

  MyMap::Iterator mit(m1);

  while(mit.hasNext())
  {
    unsigned k=mit.nextKey();
    unsigned v;
    ALWAYS(m1.find(k,v));
  }
  ASS(!m1.find(4));
  ASS(m1.find(5));

  m1.reset();
  MyMap::Iterator mit2(m1);
  while(mit2.hasNext())
  {
    ASSERTION_VIOLATION;
  }

  ASS(m1.isEmpty());
  m1.reset();
  ASS(m1.isEmpty());

  unsigned cnt=10000;
  for(unsigned i=0;i<cnt;i++) {
    m1.insert(i,i*i);
  }
  ASS_EQ(m1.size(),cnt);
  for(unsigned i=0;i<cnt;i++) {
    unsigned v;
    ALWAYS(m1.find(i,v));
    ASS_EQ(v,i*i);
  }
  ASS(!m1.find(cnt));

  for(unsigned i=1;i<cnt;i+=2) {
    ALWAYS(m1.remove(i));
  }
  NEVER(m1.remove(cnt+1));
  ASS_EQ(m1.size(), cnt/2+cnt%2);
  for(unsigned i=0;i<cnt;i++) {
    unsigned v;
    bool res=m1.find(i,v);

    ASS(res==(i%2==0));
    ASS(!res||v==i*i);
  }
}

