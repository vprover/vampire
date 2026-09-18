/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Formula.hpp"

using namespace Kernel;

// Terms and predicate arguments use different output routines.
static void checkPrinted(TermList term, TermList sort, const std::string& expected)
{
  ASS_EQ(term.toString(), expected);

  auto wrap = FuncSugar("wrap", {sort}, sort);
  TermList wrapped(Term::create(wrap.functor(), {term}));
  ASS_EQ(wrapped.toString(), "wrap(" + expected + ")");

  auto pred = PredSugar("pred", {sort, sort});
  TermList args[] = {term, wrapped};
  Literal* literal = Literal::create(pred.functor(), 2, true, args);
  ASS_EQ(literal->toString(), "pred(" + expected + ",wrap(" + expected + "))");
}

TEST_FUN(ordinary_term_output)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_FUNC(f, {sort, sort}, sort)
  checkPrinted(a, sort, "a");
  checkPrinted(f(a, TermList::var(0)), sort, "f(a,X0)");
}

TEST_FUN(ite_output)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  DECL_PRED(p, {})
  auto condition = new AtomicFormula(p());
  TermList ite(Term::createITE(condition, a, b, sort));
  checkPrinted(ite, sort, "$ite(p, a,b)");
  TermList nested(Term::createITE(condition, ite, a, sort));
  checkPrinted(nested, sort, "$ite(p, $ite(p, a,b),a)");
}

TEST_FUN(let_output)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(x, sort)
  DECL_FUNC(f, {sort, sort}, sort)
  auto binding = Formula::createDefinition(x.sugaredExpr().term(), a);
  TermList let(Term::createLet(binding, f(x, x), sort));
  checkPrinted(let, sort, "$let(x: $i, x := a, f(x,x))");

  TermList ite(Term::createITE(Formula::trueFormula(), let, a, sort));
  checkPrinted(ite, sort, "$ite($true, $let(x: $i, x := a, f(x,x)),a)");
  TermList nested(Term::createLet(binding, ite, sort));
  checkPrinted(nested, sort, "$let(x: $i, x := a, $ite($true, $let(x: $i, x := a, f(x,x)),a))");
}

TEST_FUN(match_output)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_CONST(b, sort)
  TermList args[] = {a, a, b};
  checkPrinted(TermList(Term::createMatch(sort, sort, 3, args)), sort, "$match(a,a,b)");
}

TEST_FUN(formula_term_output)
{
  auto sort = AtomicSort::boolSort();
  checkPrinted(TermList(Term::createFormula(Formula::trueFormula())), sort, "$true");
}

TEST_FUN(lambda_output)
{
  auto sort = AtomicSort::defaultSort();
  auto vars = VSList::singleton({0, sort});
  TermList lambda(Term::createLambda(TermList::var(0), vars, sort));
  checkPrinted(lambda, AtomicSort::arrowSort(sort, sort), "(^[X0 : $i] : (X0))");
}
