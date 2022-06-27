/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/DHMap.hpp"
#include "Test/UnitTesting.hpp"

typedef DHMap<unsigned, unsigned> MyMap;

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

