/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "PolynomialMultiplication.hpp"
#include "Kernel/PolynomialNormalizer.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Inferences {

SimplifyingGeneratingLiteralSimplification::Result PolynomialMultiplication::simplifyLiteral(Literal* l)
{
  // CHECK OUT:
  // We use the CALL(...) macro to trace function calls. You will see a stack of calls when an assertio is being violated.
  CALL("PolynomialMultiplication::simplifyLiteral(Literal* l)");
  
  Stack<TermList> simplArgs(l->arity());
  for (unsigned i = 0; i < l->arity(); i++) {
    // CHECK OUT:
    // we have a special datastructure for arithmetic terms, called PolyNF. 
    // Have a look at Kernel/Polynomial.hpp
    // Terms are converted to this normal using normalizerTerm
    auto term = simplNormalizeTerm(TypedTermList(*l->nthArgument(i), SortHelper::getArgSort(l, i)));
    // CHECK OUT:
    // we do not wanna use recursion due to "problems with stack overflows in the past". So we use an explicit 
    // stack for recursion instead. For many common cases this can be handled using the function evaluateBottomUp
    // Have a look at the file Kernel/BottomUpEvaluation.hpp, and UnitTests/tBottomUpEvaluation.cpp
    auto simpl = evaluateBottomUp(term, Evaluator{ *this });
    simplArgs.push(simpl.denormalize());
  }
  return Result::literal(Literal::create(l, simplArgs.begin()));
}

Kernel::PolyNf PolynomialMultiplication::evaluateStep(Kernel::PolyNf origTerm, Kernel::PolyNf* evalutedArgs)
{
  CALL("evaluateStep(Kernel::PolyNf origTerm, Kernel::PolyNf* evalutedArgs)");
  // TODO implement me
  // 1) use the macros ASS, ASS_REP, ASS_EQ, ASS_L, and friends, defined in Lib/Assertion.hpp
  // 2) use the macros DBG to print debug output and DBGE to print an expression (`DBGE(x)` prints "x = <value of x>")
  ASSERTION_VIOLATION
}



} // namespace Inferences 
