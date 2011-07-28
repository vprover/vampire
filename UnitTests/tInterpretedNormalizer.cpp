
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
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
  unsigned succ = theory->getFnNum(Theory::INT_SUCCESSOR);
  TermList two(theory->representConstant(IntegerConstantType(2)));
  TermList twoS(Term::create1(succ, two));
  Literal* lit = Literal::createEquality(true, twoS, twoS);
  Clause* cl = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, new Inference(Inference::INPUT));
  cout << cl->toString() << endl;

  InterpretedNormalizer inorm;
  Clause* norm = inorm.apply(cl);
  cout << norm->toString() << endl;
}
