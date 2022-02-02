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

#include "Lib/DHMultiset.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

class IdHash {
public:
  static unsigned hash(int i)
  {
    return i;
  }
};

class ConstHash {
public:
  static unsigned hash(int i)
  {
    return 1;
  }
};

//typedef DHMultiset<int, ConstHash, IdHash> MySet;
typedef DHMultiset<int> MySet;

TEST_FUN(dhmultiset1)
{
  MySet m1;

  //cnt has to be even number
  int cnt=10000;

  for(int i=0;i<cnt;i++) {
    m1.insert(i);
    if(i%1000==0) {
      ASSERT_VALID(m1);
    }
  }
  ASS_EQ(m1.size(), cnt);
  for(int i=0;i<cnt;i++) {
    ASS(m1.find(i));
  }
  ASS(!m1.find(cnt));
  ASSERT_VALID(m1);

  for(int i=1;i<cnt;i+=2) {
    m1.remove(i);
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
    m1.insert(i-1);
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
  }
  ASS_EQ(m1.size(), cnt);
  for(int i=0;i<cnt;i++) {
    ASS_EQ(m1.find(i),(i%2==0));
  }
  for(int i=0;i<cnt;i+=2) {
    m1.remove(i);
    ASS(m1.find(i));
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
    m1.remove(i);
    ASS(!m1.find(i));
    if(i%1000<5) {
      ASSERT_VALID(m1);
    }
  }
  ASS_EQ(m1.size(),0);
}
