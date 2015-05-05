#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Inferences/Instantiation.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID inst 
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Inferences;


TEST_FUN(instances)
{

  unsigned mult = theory->getFnNum(Theory::INT_MULTIPLY);
  TermList two(theory->representConstant(IntegerConstantType("2")));
  TermList five(theory->representConstant(IntegerConstantType("5")));
  TermList x(1,false);
  TermList multTwoX(Term::create2(mult, two, x));
  Literal* lit = Literal::createEquality(true, multTwoX, five, Sorts::SRT_INTEGER);

  Clause * cl = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::INPUT));
  (* cl)[0] = lit;

  Instantiation inst;
  cout << "GENERATING" << endl;
  ClauseIterator clauses = inst.generateClauses(cl);
  while(clauses.hasNext()){ cout << clauses.next()->toString() << endl; }

}

