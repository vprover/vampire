
/*
 * File tInstantiation.cpp.
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


#warning Compile-time broken test: instances
/*
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

  TermList twenty(theory->representConstant(IntegerConstantType("20")));
  Literal* l2 = Literal::createEquality(true,twenty,twenty,Sorts::SRT_INTEGER);
  Clause* cl2 = new(1) Clause(1,Unit::AXIOM,new Inference(Inference::INPUT));
  (* cl2)[0] = l2;

  Instantiation inst;
  inst.registerClause(cl2);
  ClauseIterator clauses = inst.generateClauses(cl);
  while(clauses.hasNext()){ cout << clauses.next()->toString() << endl; }

}
*/
