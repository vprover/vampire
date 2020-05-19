
/*
 * File tInterpretedNormalizer.cpp.
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

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Shell/InterpretedNormalizer.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID interpNorm
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;


TEST_FUN(interpNorm1)
{
  unsigned succ = env.signature->getInterpretingSymbol(Theory::INT_SUCCESSOR);
  TermList two(theory->representConstant(IntegerConstantType(2)));
  TermList twoS(Term::create1(succ, two));
  Literal* lit = Literal::createEquality(true, twoS, twoS, Sorts::SRT_INTEGER);
  Clause* cl = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, new Inference0(Inference::INPUT));
  cout << cl->toString() << endl;

  Problem prb(pvi(getSingletonIterator(cl)), false);

  InterpretedNormalizer inorm;
  inorm.apply(prb);
  Clause* norm = static_cast<Clause*>(prb.units()->head());
  cout << norm->toString() << endl;
}
