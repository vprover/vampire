
/*
 * File tDisagreement.cpp.
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
#include <iostream>

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID disagreement
UT_CREATE;

using namespace std;
using namespace Lib;

using namespace Kernel;

TEST_FUN(dis1)
{

  unsigned p = env.signature->addFunction("p",1);
  TermList x(0,false);
  TermList y(1,false);
  Term* px = Term::create1(p,x);
  Term* py = Term::create1(p,y);

  cout << endl;

  static DisagreementSetIterator dsit;
  dsit.reset(px, py, true);

  ASS(dsit.hasNext());

  pair<TermList, TermList> diff=dsit.next();
  TermList st1=diff.first;
  TermList st2=diff.second;

  ASS(st1 == x)
  ASS(st2 == y)
  ASS(!dsit.hasNext())
}
