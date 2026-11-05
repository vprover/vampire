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

#define SUGAR        \
  DECL_DEFAULT_SORT  \
  DECL_SORT_BOOL     \
  DECL_DEFAULT_VARS  \
  DECL_PRED(p, {})   \
  DECL_PRED(q, {})   \
  DECL_PRED(r, {ds}) \
  DECL_CONST(a, ds)  \
  DECL_CONST(b, ds)  \

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
  DECL_FUNC(f, {ds, ds}, ds)
  checkPrinted(a, ds, "a");
  checkPrinted(f(a, TermList::var(0)), ds, "f(a,X0)");
)

TEST_OUTPUT(ite_output,
  auto condition = new AtomicFormula(p());
  auto inner = ite(condition, a, b);
  checkPrinted(inner, ds, "$ite(p, a,b)");
  checkPrinted(ite(condition, inner, a), ds, "$ite(p, $ite(p, a,b),a)");
)

TEST_OUTPUT(let_output,
  DECL_FUNC(f, {ds, ds}, ds)
  auto binding = Formula::createDefinition(b.sugaredExpr().term(), a);
  TermList let(Term::createLet(binding, f(b, b), ds));
  checkPrinted(let, ds, "$let(b: $i, b := a, f(b,b))");

  auto inner = ite(trueF(), let, a);
  checkPrinted(inner, ds, "$ite($true, $let(b: $i, b := a, f(b,b)),a)");
  TermList nested(Term::createLet(binding, inner, ds));
  checkPrinted(nested, ds, "$let(b: $i, b := a, $ite($true, $let(b: $i, b := a, f(b,b)),a))");
)

TEST_OUTPUT(match_output,
  TermList args[] = {a, a, b};
  checkPrinted(TermList(Term::createMatch(ds, ds, 3, args)), ds, "$match(a,a,b)");
)

TEST_OUTPUT(formula_term_output,
  checkPrinted(termF(trueF()), Bool, "$true");
)

TEST_OUTPUT(lambda_output,
  auto vars = VSList::singleton({x.sugaredExpr().var(), ds});
  TermList lambda(Term::createLambda(x, vars, ds));
  checkPrinted(lambda, arrow(ds, ds), "(^[X0 : $i] : (X0))");
)

// formula symbol precedences

// outer negation

#define TEST_PRECEDENCE_NEGATION(name, f, exp) \
  TEST_OUTPUT(negation_##name, checkPrinted(termF(~f), Bool, exp); \
)

TEST_PRECEDENCE_NEGATION(var, boolT(x), "~ X0")
TEST_PRECEDENCE_NEGATION(equality, atom(a == b), "~ a = b")
TEST_PRECEDENCE_NEGATION(predicate, atom(r(a)), "~ r(a)")
TEST_PRECEDENCE_NEGATION(negation, ~atom(p()), "~ ~ p")
TEST_PRECEDENCE_NEGATION(trueF, trueF(), "~ $true")
TEST_PRECEDENCE_NEGATION(falseF, falseF(), "~ $false")
TEST_PRECEDENCE_NEGATION(named, nameF("name"), "~ name")
TEST_PRECEDENCE_NEGATION(forall, forall(x.sort(ds), atom(r(x))), "~ ! [X0] : r(X0)")
TEST_PRECEDENCE_NEGATION(exists, exists(x.sort(ds), atom(r(x))), "~ ? [X0] : r(X0)")
TEST_PRECEDENCE_NEGATION(conj, conj({ atom(p()), atom(q()) }), "~ (p & q)")
TEST_PRECEDENCE_NEGATION(disj, disj({ atom(p()), atom(q()) }), "~ (p | q)")
TEST_PRECEDENCE_NEGATION(impl, impl(atom(p()), atom(q())), "~ (p => q)")
TEST_PRECEDENCE_NEGATION(equiv, equiv(atom(p()), atom(q())), "~ (p <=> q)")
TEST_PRECEDENCE_NEGATION(xorr, xorr(atom(p()), atom(q())), "~ (p <~> q)")

// outer conjunction

#define TEST_PRECEDENCE_CONJ(name, f, exp) \
  TEST_OUTPUT(conj_##name, checkPrinted(termF(conj({ atom(p()), f, atom(q()) })), Bool, exp); \
)

TEST_PRECEDENCE_CONJ(var, boolT(x), "p & X0 & q")
TEST_PRECEDENCE_CONJ(equality, atom(a == b), "p & a = b & q")
TEST_PRECEDENCE_CONJ(predicate, atom(r(a)), "p & r(a) & q")
TEST_PRECEDENCE_CONJ(negation, ~atom(p()), "p & ~ p & q")
TEST_PRECEDENCE_CONJ(trueF, trueF(), "p & $true & q")
TEST_PRECEDENCE_CONJ(falseF, falseF(), "p & $false & q")
TEST_PRECEDENCE_CONJ(named, nameF("name"), "p & name & q")
TEST_PRECEDENCE_CONJ(forall, forall(x.sort(ds), atom(r(x))), "p & ! [X0] : r(X0) & q")
TEST_PRECEDENCE_CONJ(exists, exists(x.sort(ds), atom(r(x))), "p & ? [X0] : r(X0) & q")
TEST_PRECEDENCE_CONJ(conj, conj({ atom(p()), atom(q()) }), "p & (p & q) & q")
TEST_PRECEDENCE_CONJ(disj, disj({ atom(p()), atom(q()) }), "p & (p | q) & q")
TEST_PRECEDENCE_CONJ(impl, impl(atom(p()), atom(q())), "p & (p => q) & q")
TEST_PRECEDENCE_CONJ(equiv, equiv(atom(p()), atom(q())), "p & (p <=> q) & q")
TEST_PRECEDENCE_CONJ(xorr, xorr(atom(p()), atom(q())), "p & (p <~> q) & q")

// outer disjunction

#define TEST_PRECEDENCE_DISJ(name, f, exp) \
  TEST_OUTPUT(disj_##name, checkPrinted(termF(disj({ atom(p()), f, atom(q()) })), Bool, exp); \
)

TEST_PRECEDENCE_DISJ(var, boolT(x), "p | X0 | q")
TEST_PRECEDENCE_DISJ(equality, atom(a == b), "p | a = b | q")
TEST_PRECEDENCE_DISJ(predicate, atom(r(a)), "p | r(a) | q")
TEST_PRECEDENCE_DISJ(negation, ~atom(p()), "p | ~ p | q")
TEST_PRECEDENCE_DISJ(trueF, trueF(), "p | $true | q")
TEST_PRECEDENCE_DISJ(falseF, falseF(), "p | $false | q")
TEST_PRECEDENCE_DISJ(named, nameF("name"), "p | name | q")
TEST_PRECEDENCE_DISJ(forall, forall(x.sort(ds), atom(r(x))), "p | ! [X0] : r(X0) | q")
TEST_PRECEDENCE_DISJ(exists, exists(x.sort(ds), atom(r(x))), "p | ? [X0] : r(X0) | q")
TEST_PRECEDENCE_DISJ(conj, conj({ atom(p()), atom(q()) }), "p | (p & q) | q")
TEST_PRECEDENCE_DISJ(disj, disj({ atom(p()), atom(q()) }), "p | (p | q) | q")
TEST_PRECEDENCE_DISJ(impl, impl(atom(p()), atom(q())), "p | (p => q) | q")
TEST_PRECEDENCE_DISJ(equiv, equiv(atom(p()), atom(q())), "p | (p <=> q) | q")
TEST_PRECEDENCE_DISJ(xorr, xorr(atom(p()), atom(q())), "p | (p <~> q) | q")

// outer forall

#define TEST_PRECEDENCE_FORALL(name, f, exp) \
  TEST_OUTPUT(forall_##name, checkPrinted(termF(forall(y.sort(ds), f)), Bool, exp); \
)

TEST_PRECEDENCE_FORALL(var, boolT(x), "! [X1] : X0")
TEST_PRECEDENCE_FORALL(equality, atom(a == b), "! [X1] : a = b")
TEST_PRECEDENCE_FORALL(predicate, atom(r(a)), "! [X1] : r(a)" )
TEST_PRECEDENCE_FORALL(negation, ~atom(p()), "! [X1] : ~ p" )
TEST_PRECEDENCE_FORALL(trueF, trueF(), "! [X1] : $true" )
TEST_PRECEDENCE_FORALL(falseF, falseF(), "! [X1] : $false" )
TEST_PRECEDENCE_FORALL(named, nameF("name"), "! [X1] : name" )
TEST_PRECEDENCE_FORALL(forall, forall(x.sort(ds), atom(r(x))), "! [X1] : ! [X0] : r(X0)" )
TEST_PRECEDENCE_FORALL(exists, exists(x.sort(ds), atom(r(x))), "! [X1] : ? [X0] : r(X0)" )
TEST_PRECEDENCE_FORALL(conj, conj({ atom(p()), atom(q()) }), "! [X1] : (p & q)" )
TEST_PRECEDENCE_FORALL(disj, disj({ atom(p()), atom(q()) }), "! [X1] : (p | q)" )
TEST_PRECEDENCE_FORALL(impl, impl(atom(p()), atom(q())), "! [X1] : (p => q)" )
TEST_PRECEDENCE_FORALL(equiv, equiv(atom(p()), atom(q())), "! [X1] : (p <=> q)" )
TEST_PRECEDENCE_FORALL(xorr, xorr(atom(p()), atom(q())), "! [X1] : (p <~> q)" )

// outer forall

#define TEST_PRECEDENCE_EXISTS(name, f, exp) \
  TEST_OUTPUT(exists_##name, checkPrinted(termF(exists(y.sort(ds), f)), Bool, exp); \
)

TEST_PRECEDENCE_EXISTS(var, boolT(x), "? [X1] : X0")
TEST_PRECEDENCE_EXISTS(equality, atom(a == b), "? [X1] : a = b")
TEST_PRECEDENCE_EXISTS(predicate, atom(r(a)), "? [X1] : r(a)" )
TEST_PRECEDENCE_EXISTS(negation, ~atom(p()), "? [X1] : ~ p" )
TEST_PRECEDENCE_EXISTS(trueF, trueF(), "? [X1] : $true" )
TEST_PRECEDENCE_EXISTS(falseF, falseF(), "? [X1] : $false" )
TEST_PRECEDENCE_EXISTS(named, nameF("name"), "? [X1] : name" )
TEST_PRECEDENCE_EXISTS(forall, forall(x.sort(ds), atom(r(x))), "? [X1] : ! [X0] : r(X0)" )
TEST_PRECEDENCE_EXISTS(exists, exists(x.sort(ds), atom(r(x))), "? [X1] : ? [X0] : r(X0)" )
TEST_PRECEDENCE_EXISTS(conj, conj({ atom(p()), atom(q()) }), "? [X1] : (p & q)" )
TEST_PRECEDENCE_EXISTS(disj, disj({ atom(p()), atom(q()) }), "? [X1] : (p | q)" )
TEST_PRECEDENCE_EXISTS(impl, impl(atom(p()), atom(q())), "? [X1] : (p => q)" )
TEST_PRECEDENCE_EXISTS(equiv, equiv(atom(p()), atom(q())), "? [X1] : (p <=> q)" )
TEST_PRECEDENCE_EXISTS(xorr, xorr(atom(p()), atom(q())), "? [X1] : (p <~> q)" )

// outer implication (left)

#define TEST_PRECEDENCE_IMPL_LEFT(name, f, exp) \
  TEST_OUTPUT(impl_left_##name, checkPrinted(termF(impl(f, atom(q()))), Bool, exp); \
)

TEST_PRECEDENCE_IMPL_LEFT(var, boolT(x), "X0 => q")
TEST_PRECEDENCE_IMPL_LEFT(equality, atom(a == b), "a = b => q")
TEST_PRECEDENCE_IMPL_LEFT(predicate, atom(r(a)), "r(a) => q")
TEST_PRECEDENCE_IMPL_LEFT(negation, ~atom(p()), "~ p => q")
TEST_PRECEDENCE_IMPL_LEFT(trueF, trueF(), "$true => q")
TEST_PRECEDENCE_IMPL_LEFT(falseF, falseF(), "$false => q")
TEST_PRECEDENCE_IMPL_LEFT(named, nameF("name"), "name => q")
TEST_PRECEDENCE_IMPL_LEFT(forall, forall(x.sort(ds), atom(r(x))), "! [X0] : r(X0) => q")
TEST_PRECEDENCE_IMPL_LEFT(exists, exists(x.sort(ds), atom(r(x))), "? [X0] : r(X0) => q")
TEST_PRECEDENCE_IMPL_LEFT(conj, conj({ atom(p()), atom(q()) }), "(p & q) => q")
TEST_PRECEDENCE_IMPL_LEFT(disj, disj({ atom(p()), atom(q()) }), "(p | q) => q")
TEST_PRECEDENCE_IMPL_LEFT(impl, impl(atom(p()), atom(q())), "(p => q) => q")
TEST_PRECEDENCE_IMPL_LEFT(equiv, equiv(atom(p()), atom(q())), "(p <=> q) => q")
TEST_PRECEDENCE_IMPL_LEFT(xorr, xorr(atom(p()), atom(q())), "(p <~> q) => q")

// outer implication (right)

#define TEST_PRECEDENCE_IMPL_RIGHT(name, f, exp) \
  TEST_OUTPUT(impl_right_##name, checkPrinted(termF(impl(atom(p()), f)), Bool, exp); \
)

TEST_PRECEDENCE_IMPL_RIGHT(var, boolT(x), "p => X0")
TEST_PRECEDENCE_IMPL_RIGHT(equality, atom(a == b), "p => a = b")
TEST_PRECEDENCE_IMPL_RIGHT(predicate, atom(r(a)), "p => r(a)")
TEST_PRECEDENCE_IMPL_RIGHT(negation, ~atom(p()), "p => ~ p")
TEST_PRECEDENCE_IMPL_RIGHT(trueF, trueF(), "p => $true")
TEST_PRECEDENCE_IMPL_RIGHT(falseF, falseF(), "p => $false")
TEST_PRECEDENCE_IMPL_RIGHT(named, nameF("name"), "p => name")
TEST_PRECEDENCE_IMPL_RIGHT(forall, forall(x.sort(ds), atom(r(x))), "p => ! [X0] : r(X0)")
TEST_PRECEDENCE_IMPL_RIGHT(exists, exists(x.sort(ds), atom(r(x))), "p => ? [X0] : r(X0)")
TEST_PRECEDENCE_IMPL_RIGHT(conj, conj({ atom(p()), atom(q()) }), "p => (p & q)")
TEST_PRECEDENCE_IMPL_RIGHT(disj, disj({ atom(p()), atom(q()) }), "p => (p | q)")
TEST_PRECEDENCE_IMPL_RIGHT(impl, impl(atom(p()), atom(q())), "p => (p => q)")
TEST_PRECEDENCE_IMPL_RIGHT(equiv, equiv(atom(p()), atom(q())), "p => (p <=> q)")
TEST_PRECEDENCE_IMPL_RIGHT(xorr, xorr(atom(p()), atom(q())), "p => (p <~> q)")

// outer equivalence

#define TEST_PRECEDENCE_EQUIV(name, f, exp) \
  TEST_OUTPUT(equiv_##name, checkPrinted(termF(equiv(atom(p()), f)), Bool, exp); \
)

TEST_PRECEDENCE_EQUIV(var, boolT(x), "p <=> X0")
TEST_PRECEDENCE_EQUIV(equality, atom(a == b), "p <=> a = b")
TEST_PRECEDENCE_EQUIV(predicate, atom(r(a)), "p <=> r(a)")
TEST_PRECEDENCE_EQUIV(negation, ~atom(p()), "p <=> ~ p")
TEST_PRECEDENCE_EQUIV(trueF, trueF(), "p <=> $true")
TEST_PRECEDENCE_EQUIV(falseF, falseF(), "p <=> $false")
TEST_PRECEDENCE_EQUIV(named, nameF("name"), "p <=> name")
TEST_PRECEDENCE_EQUIV(forall, forall(x.sort(ds), atom(r(x))), "p <=> ! [X0] : r(X0)")
TEST_PRECEDENCE_EQUIV(exists, exists(x.sort(ds), atom(r(x))), "p <=> ? [X0] : r(X0)")
TEST_PRECEDENCE_EQUIV(conj, conj({ atom(p()), atom(q()) }), "p <=> (p & q)")
TEST_PRECEDENCE_EQUIV(disj, disj({ atom(p()), atom(q()) }), "p <=> (p | q)")
TEST_PRECEDENCE_EQUIV(impl, impl(atom(p()), atom(q())), "p <=> (p => q)")
TEST_PRECEDENCE_EQUIV(equiv, equiv(atom(p()), atom(q())), "p <=> (p <=> q)")
TEST_PRECEDENCE_EQUIV(xorr, xorr(atom(p()), atom(q())), "p <=> (p <~> q)")

// outer xor

#define TEST_PRECEDENCE_XOR(name, f, exp) \
  TEST_OUTPUT(xor_##name, checkPrinted(termF(xorr(atom(p()), f)), Bool, exp); \
)

TEST_PRECEDENCE_XOR(var, boolT(x), "p <~> X0")
TEST_PRECEDENCE_XOR(equality, atom(a == b), "p <~> a = b")
TEST_PRECEDENCE_XOR(predicate, atom(r(a)), "p <~> r(a)")
TEST_PRECEDENCE_XOR(negation, ~atom(p()), "p <~> ~ p")
TEST_PRECEDENCE_XOR(trueF, trueF(), "p <~> $true")
TEST_PRECEDENCE_XOR(falseF, falseF(), "p <~> $false")
TEST_PRECEDENCE_XOR(named, nameF("name"), "p <~> name")
TEST_PRECEDENCE_XOR(forall, forall(x.sort(ds), atom(r(x))), "p <~> ! [X0] : r(X0)")
TEST_PRECEDENCE_XOR(exists, exists(x.sort(ds), atom(r(x))), "p <~> ? [X0] : r(X0)")
TEST_PRECEDENCE_XOR(conj, conj({ atom(p()), atom(q()) }), "p <~> (p & q)")
TEST_PRECEDENCE_XOR(disj, disj({ atom(p()), atom(q()) }), "p <~> (p | q)")
TEST_PRECEDENCE_XOR(impl, impl(atom(p()), atom(q())), "p <~> (p => q)")
TEST_PRECEDENCE_XOR(equiv, equiv(atom(p()), atom(q())), "p <~> (p <=> q)")
TEST_PRECEDENCE_XOR(xorr, xorr(atom(p()), atom(q())), "p <~> (p <~> q)")

// outer equality

#define TEST_PRECEDENCE_EQUALITY(name, f, exp) \
  TEST_OUTPUT(equality_##name, checkPrinted(termF(atom(termF(f) == termF(atom(q())))), Bool, exp); \
)

TEST_PRECEDENCE_EQUALITY(var, boolT(x), "(X0 = q)")
TEST_PRECEDENCE_EQUALITY(equality, atom(a == b), "(a = b = q)")
TEST_PRECEDENCE_EQUALITY(predicate, atom(r(a)), "(r(a) = q)")
TEST_PRECEDENCE_EQUALITY(negation, ~atom(p()), "(~ p = q)")
TEST_PRECEDENCE_EQUALITY(trueF, trueF(), "($true = q)")
TEST_PRECEDENCE_EQUALITY(falseF, falseF(), "($false = q)")
TEST_PRECEDENCE_EQUALITY(named, nameF("name"), "(name = q)")
TEST_PRECEDENCE_EQUALITY(forall, forall(x.sort(ds), atom(r(x))), "(! [X0] : r(X0) = q)")
TEST_PRECEDENCE_EQUALITY(exists, exists(x.sort(ds), atom(r(x))), "(? [X0] : r(X0) = q)")
TEST_PRECEDENCE_EQUALITY(conj, conj({ atom(p()), atom(q()) }), "(p & q = q)")
TEST_PRECEDENCE_EQUALITY(disj, disj({ atom(p()), atom(q()) }), "(p | q = q)")
TEST_PRECEDENCE_EQUALITY(impl, impl(atom(p()), atom(q())), "(p => q = q)")
TEST_PRECEDENCE_EQUALITY(equiv, equiv(atom(p()), atom(q())), "(p <=> q = q)")
TEST_PRECEDENCE_EQUALITY(xorr, xorr(atom(p()), atom(q())), "(p <~> q = q)")

// higher-order printing

#define HOL_SUGAR                    \
  DECL_DEFAULT_SORT                  \
  DECL_SORT_BOOL                     \
  DECL_DEFAULT_VARS                  \
  DECL_CONST(p, Bool)                \
  DECL_CONST(q, Bool)                \
  TermStack p_args = {p, q};         \
  DECL_CONST(a, ds)                  \
  DECL_CONST(b, ds)                  \
  TermStack t_args = {a, b};         \
  DECL_CONST(f, arrow({ds, ds}, ds)) \
  DECL_OR_PROXY                      \
  DECL_AND_PROXY                     \
  DECL_IMP_PROXY                     \
  DECL_EQ_PROXY                      \
  DECL_IFF_PROXY                     \
  DECL_PI_PROXY                      \
  DECL_SIGMA_PROXY                   \
  DECL_NOT_PROXY                     \
  DECL_XOR_PROXY

// Terms and predicate arguments use different output routines.
static void checkPrintedHOL(TermList term, TermList sort, const std::string& expected)
{
  ASS_EQ(term.toString(), expected);

  TermList wrapped = ap(ConstSugar("wrap", arrow(sort, sort)), {term});
  ASS_EQ(wrapped.toString(), "(wrap @ " + expected + ")");
}

TEST_FUN(equality_application) {
  __ALLOW_UNUSED(HOL_SUGAR);
  env.setHigherOrder(true);
  checkPrintedHOL(termF(atom(ap(f, {x, y}) == x)), Bool, "((((f @ X0 @ X1)) = X0))");
}

TEST_FUN(equality_lambda) {
  __ALLOW_UNUSED(HOL_SUGAR);
  env.setHigherOrder(true);
  checkPrintedHOL(termF(atom(lam(ds, ap(f, x)) == y)), Bool, "(((^[Y0 : $i]: (f @ X0)) = X1))");
}

#define TEST_OUTPUT_PROXY(name, proxy, args, exp)           \
  TEST_FUN(partially_applied_proxy_##name) {                \
    __ALLOW_UNUSED(HOL_SUGAR);                              \
    auto _args = TermStack(args);                           \
    env.setHigherOrder(true);                               \
    auto sort = proxy.sort();                               \
    for (const auto& _ : _args) sort = sort.result();       \
    DECL_CONST(g, arrow({ds, sort}, ds))                    \
    checkPrintedHOL(ap(g, {x, ap(proxy, _args)}), ds, exp); \
}

// 0 arguments
TEST_OUTPUT_PROXY(orP_0, orP, {}, "(g @ X0 @ |)")
TEST_OUTPUT_PROXY(andP_0, andP, {}, "(g @ X0 @ &)")
TEST_OUTPUT_PROXY(impP_0, impP, {}, "(g @ X0 @ =>)")
TEST_OUTPUT_PROXY(eqP_0, eqP(AtomicSort::defaultSort()), {}, "(g @ X0 @ =)")
TEST_OUTPUT_PROXY(iffP_0, iffP, {}, "(g @ X0 @ =)")
TEST_OUTPUT_PROXY(piP_0, piP(AtomicSort::defaultSort()), {}, "(g @ X0 @ !! @ $i)")
TEST_OUTPUT_PROXY(sigmaP_0, sigmaP(AtomicSort::defaultSort()), {}, "(g @ X0 @ ?? @ $i)")
TEST_OUTPUT_PROXY(notP_0, notP, {}, "(g @ X0 @ ~)")
TEST_OUTPUT_PROXY(xorP_0, xorP, {}, "(g @ X0 @ <~>)")

// 1 arguments
TEST_OUTPUT_PROXY(orP_1, orP, {p}, "(g @ X0 @ (| @ p))")
TEST_OUTPUT_PROXY(andP_1, andP, {p}, "(g @ X0 @ (& @ p))")
TEST_OUTPUT_PROXY(impP_1, impP, {p}, "(g @ X0 @ (=> @ p))")
TEST_OUTPUT_PROXY(eqP_1, eqP(AtomicSort::defaultSort()), {a}, "(g @ X0 @ (= @ a))")
TEST_OUTPUT_PROXY(iffP_1, iffP, {p}, "(g @ X0 @ (= @ p))")
TEST_OUTPUT_PROXY(piP_1, piP(AtomicSort::defaultSort()), {lam(ds, p)}, "(g @ X0 @ (!! @ $i @ (^[Y0 : $i]: (p))))")
TEST_OUTPUT_PROXY(sigmaP_1, sigmaP(AtomicSort::defaultSort()), {lam(ds, p)}, "(g @ X0 @ (?? @ $i @ (^[Y0 : $i]: (p))))")
TEST_OUTPUT_PROXY(notP_1, notP, {p}, "(g @ X0 @ (~ p))")
TEST_OUTPUT_PROXY(xorP_1, xorP, {p}, "(g @ X0 @ (<~> @ p))")

// 2 arguments
TEST_OUTPUT_PROXY(orP_2, orP, p_args, "(g @ X0 @ (p | q))")
TEST_OUTPUT_PROXY(andP_2, andP, p_args, "(g @ X0 @ (p & q))")
TEST_OUTPUT_PROXY(impP_2, impP, p_args, "(g @ X0 @ (p => q))")
TEST_OUTPUT_PROXY(eqP_2, eqP(AtomicSort::defaultSort()), t_args, "(g @ X0 @ (a = b))")
TEST_OUTPUT_PROXY(iffP_2, iffP, p_args, "(g @ X0 @ (p = q))")
TEST_OUTPUT_PROXY(xorP_2, xorP, p_args, "(g @ X0 @ (p <~> q))")