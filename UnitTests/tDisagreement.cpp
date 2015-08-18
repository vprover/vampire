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
  dsit.reset(px, px, true);

  while (dsit.hasNext()) {
    pair<TermList, TermList> diff=dsit.next();
    TermList st1=diff.first;
    TermList st2=diff.second;

    cout << "st1 " << st1.toString() << endl;
    cout << "st2 " << st2.toString() << endl;
  }

}
