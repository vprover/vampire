
/*
 * File tInterpretedFunctions.cpp.
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

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Kernel/InterpretedLiteralEvaluator.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID interpFunc
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;


void interpret(Literal* lit)
{
  cout << endl;
  cout << "Start with: " << lit->toString() << endl;

  InterpretedLiteralEvaluator* eval = new InterpretedLiteralEvaluator();

  bool constant;
  Literal* res;
  bool constantTrue;

  eval->evaluate(lit,constant,res,constantTrue);

  cout << "constant="<<constant<<",constantTrue="<<constantTrue<<endl;
  if(res){
     cout << "res= " << res->toString() << endl;
  }else{
     cout << "res not defined" << endl;
  }
}
// Interpret x*2=5
TEST_FUN(interpFunc1)
{
  unsigned mult = env.signature->addInterpretedFunction(Theory::Interpretation::REAL_MULTIPLY, "mul");
  TermList two(theory->representConstant(RealConstantType("2")));
  TermList five(theory->representConstant(RealConstantType("5")));
  TermList x(1,false);
  TermList multTwoX(Term::create2(mult, two, x));
  Literal* lit = Literal::createEquality(true, multTwoX, five, Sorts::SRT_REAL);

  interpret(lit);
}

// Interpret 2.5*2=5
TEST_FUN(interpFunc2)
{
  unsigned mult = env.signature->addInterpretedFunction(Theory::Interpretation::REAL_MULTIPLY, "mul");
  TermList two(theory->representConstant(RealConstantType("2")));
  TermList twoHalf(theory->representConstant(RealConstantType("2.5")));
  TermList five(theory->representConstant(RealConstantType("5")));
  TermList multTwoTwoH(Term::create2(mult, two, twoHalf));
  Literal* lit = Literal::createEquality(true, multTwoTwoH, five, Sorts::SRT_REAL);

  interpret(lit);
} 

// Interpret 3*2 > 5
TEST_FUN(interpFunc3)
{
  unsigned mult = env.signature->addInterpretedFunction(Theory::Interpretation::REAL_MULTIPLY, "mul");
  TermList two(theory->representConstant(RealConstantType("2")));
  TermList three(theory->representConstant(RealConstantType("3")));
  TermList five(theory->representConstant(RealConstantType("5")));
  TermList multTwoThree(Term::create2(mult, two, three));
  unsigned greater = env.signature->addInterpretedPredicate(Theory::Interpretation::REAL_GREATER, "gt");
  // unsigned greater = theory->getPredNum(Theory::REAL_GREATER);
  Literal* lit = Literal::create2(greater,true, multTwoThree, five);

  interpret(lit);
}

// Interpret y(5)*x=5 
TEST_FUN(interpFunc4)
{

  unsigned m = env.signature->addInterpretedFunction(Theory::Interpretation::REAL_MULTIPLY, "mul");
  TermList two(theory->representConstant(RealConstantType("2")));
  TermList five(theory->representConstant(RealConstantType("5")));

  unsigned y = env.signature->addFunction("y",1);
  env.signature->getFunction(y)->setType(OperatorType::getFunctionType({ Sorts::SRT_REAL },Sorts::SRT_REAL));
  TermList y5 = TermList(Term::create1(y,five));

  TermList mult(Term::create2(m, two, y5));
  Literal* lit = Literal::createEquality(true, mult, five, Sorts::SRT_REAL);

  interpret(lit);

}
