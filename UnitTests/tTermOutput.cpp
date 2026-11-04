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

#define SUGAR       \
  DECL_SORT(s)      \
  DECL_DEFAULT_VARS \
  DECL_CONST(a, s)  \
  DECL_CONST(b, s)  \

#define TEST_OUTPUT(name, ...) \
  TEST_FUN(name) {             \
    __ALLOW_UNUSED(SUGAR)      \
    __VA_ARGS__                \
  }

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

TEST_OUTPUT(ordinary_term_output,
  DECL_FUNC(f, {s, s}, s)
  checkPrinted(a, s, "a");
  checkPrinted(f(a, TermList::var(0)), s, "f(a,X0)");
)

TEST_OUTPUT(ite_output,
  DECL_PRED(p, {})
  auto condition = new AtomicFormula(p());
  auto inner = ite(condition, a, b);
  checkPrinted(inner, s, "$ite(p, a,b)");
  checkPrinted(ite(condition, inner, a), s, "$ite(p, $ite(p, a,b),a)");
)

TEST_OUTPUT(let_output,
  DECL_FUNC(f, {s, s}, s)
  auto binding = Formula::createDefinition(b.sugaredExpr().term(), a);
  TermList let(Term::createLet(binding, f(b, b), s));
  checkPrinted(let, s, "$let(b: s, b := a, f(b,b))");

  auto inner = ite(Formula::trueFormula(), let, a);
  checkPrinted(inner, s, "$ite($true, $let(b: s, b := a, f(b,b)),a)");
  TermList nested(Term::createLet(binding, inner, s));
  checkPrinted(nested, s, "$let(b: s, b := a, $ite($true, $let(b: s, b := a, f(b,b)),a))");
)

TEST_OUTPUT(match_output,
  TermList args[] = {a, a, b};
  checkPrinted(TermList(Term::createMatch(s, s, 3, args)), s, "$match(a,a,b)");
)

TEST_OUTPUT(formula_term_output,
  checkPrinted(TermList(Term::createFormula(Formula::trueFormula())), AtomicSort::boolSort(), "$true");
)

TEST_OUTPUT(lambda_output,
  auto vars = VSList::singleton({x.sugaredExpr().var(), s});
  TermList lambda(Term::createLambda(x, vars, s));
  checkPrinted(lambda, arrow(s, s), "(^[X0 : s] : (X0))");
)
