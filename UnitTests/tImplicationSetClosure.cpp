/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/ImplicationSetClosure.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

TEST_FUN(implSetClosure1)
{
  ImplicationSetClosure<unsigned> isc;

  ASS(!isc.contains(1));
  isc.add(1);
  ASS(isc.contains(1));
  ASS(!isc.contains(2));

  isc.addImplication(1, 2);
  ASS(isc.contains(1));
  ASS(isc.contains(2));

  isc.addImplication(3, 1);
  ASS(!isc.contains(3));

  ASS(!isc.contains(4));
  ASS(!isc.contains(5));
  isc.addImplication(4, 5);
  ASS(!isc.contains(4));
  ASS(!isc.contains(5));

  isc.add(4);
  ASS(isc.contains(4));
  ASS(isc.contains(5));

  isc.addImplication(6, 7);
  isc.addImplication(6, 7);
  ASS(!isc.contains(6));
  ASS(!isc.contains(7));

  isc.addImplication(7, 8);
  isc.addImplication(8, 9);
  isc.addImplication(9, 10);
  ASS(!isc.contains(10));

  isc.add(6);
  ASS(isc.contains(10));

  isc.addImplication(11, 12);
  isc.addImplication(12, 13);
  isc.addImplication(13, 14);
  isc.addImplication(14, 15);
  isc.addImplication(15, 11);
  ASS(!isc.contains(13));
  isc.add(14);
  ASS(isc.contains(13));
}

TEST_FUN(implSetClosure2)
{
  ImplicationSetClosure<int> isc;

  int cnt=1000;
  for(int i=0; i<cnt; ++i) {
    isc.addImplication(i+1, i);
  }
  ASS(!isc.contains(0));
  ASS(!isc.contains(1001));
  isc.add(1000);
  ASS(isc.contains(0));
  ASS(isc.contains(1000));
}
