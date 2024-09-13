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

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

using namespace std;
using namespace Lib;

using namespace Kernel;

TEST_FUN(dis1)
{
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_FUNC (p, {srt}, srt)

  static DisagreementSetIterator dsit;
  dsit.reset(p(x), p(y), true);

  ASS(dsit.hasNext());

  pair<TermList, TermList> diff=dsit.next();
  TermList st1=diff.first;
  TermList st2=diff.second;

  ASS(st1 == x.sugaredExpr())
  ASS(st2 == y.sugaredExpr())
  ASS(!dsit.hasNext())
}
