/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**! Tests for the kernel-level tuple machinery (Kernel/Theory.cpp).
 *
 * Tuples are ordinary term algebras: the constructor "tuple" of an n-tuple has
 * n type arguments and n term arguments, its destructors ("proj") have n type
 * arguments and one term argument.
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

using namespace Kernel;

/** The sort Tuple(sort, ..., sort) of the given arity. */
static TermList tupleSortOf(unsigned arity, TermList sort)
{
  TermStack components;
  for (unsigned i = 0; i < arity; i++) {
    components.push(sort);
  }
  return AtomicSort::tupleSort(arity, components.begin());
}

static unsigned countTermAlgebras()
{
  unsigned count = 0;
  auto it = env.signature->termAlgebrasIterator();
  while (it.hasNext()) {
    it.next();
    count++;
  }
  return count;
}

TEST_FUN(findTupleProjection_finds_every_destructor) {
  unsigned arity = 3;
  // registers the tuple term algebra of this arity
  Theory::getTupleConstructor(arity);

  for (unsigned i = 0; i < arity; i++) {
    unsigned projFunctor = Theory::getTupleProjectionFunctor(arity, i);
    unsigned proj = arity; // deliberately out of range
    ASS_REP(Theory::findTupleProjection(projFunctor, /*isPredicate=*/false, proj),
            env.signature->functionName(projFunctor));
    ASS_EQ(proj, i);
  }
}

TEST_FUN(findTupleProjection_rejects_plain_symbols_over_tuple_sorts) {
  DECL_SORT(s)

  unsigned arity = 3;
  Theory::getTupleConstructor(arity);
  TermList tupleSort = tupleSortOf(arity, s.sugaredExpr());

  // a unary function over a tuple sort is not a projection
  DECL_FUNC(h, {tupleSort}, s)
  unsigned proj = 0;
  ASS(!Theory::findTupleProjection(h.functor(), /*isPredicate=*/false, proj));

  // and a predicate can never be one: destructors are always functions,
  // even when the projected component is Boolean
  DECL_PRED(p, {tupleSort})
  ASS(!Theory::findTupleProjection(p.functor(), /*isPredicate=*/true, proj));
}

TEST_FUN(isTupleConstructor_does_not_touch_the_signature) {
  DECL_SORT(s)

  unsigned arity = 2;
  unsigned tupleFunctor = Theory::getTupleConstructor(arity);
  TermList tupleSort = tupleSortOf(arity, s.sugaredExpr());

  DECL_CONST(g, tupleSort) // a plain constant of a tuple sort
  DECL_CONST(c, s)         // an ordinary term of a non-tuple sort

  unsigned before = countTermAlgebras();

  ASS(!Theory::isTupleConstructor(g().sugaredExpr().term()));
  ASS(!Theory::isTupleConstructor(c().sugaredExpr().term()));

  // asking whether a term is a tuple constructor must not register anything
  ASS_EQ(before, countTermAlgebras());

  // a genuine tuple term is still recognised
  TermStack args = { s.sugaredExpr(), s.sugaredExpr(), c().sugaredExpr(), c().sugaredExpr() };
  ASS(Theory::isTupleConstructor(Term::create(tupleFunctor, args)));
}

TEST_FUN(isTupleConstructor_of_a_heterogeneous_tuple) {
  NUMBER_SUGAR(Int)
  DECL_SORT(s)
  DECL_CONST(a, s)
  DECL_FUNC(f, {s}, s)
  DECL_CONST(i, Int)

  unsigned tupleFunctor = Theory::getTupleConstructor(2);

  // tuple($int, s, i, f(a)) : Tuple($int, s) -- four arguments, of which the
  // first two are the type arguments
  TermStack args = { Int.sugaredExpr(), s.sugaredExpr(), i().sugaredExpr(), f(a).sugaredExpr() };
  Term* t = Term::create(tupleFunctor, args);

  ASS_EQ(t->arity(), 4u);
  ASS_EQ(t->numTypeArguments(), 2u);

  // and the sort has exactly the tuple's arity, i.e. half of the term's
  TermList sort = SortHelper::getResultSort(t);
  ASS(sort.isTupleSort());
  ASS_EQ(sort.term()->arity(), 2u);

  ASS(Theory::isTupleConstructor(t));
}

TEST_FUN(isTupleConstructor_of_a_nested_tuple) {
  DECL_SORT(s)
  DECL_CONST(a, s)

  unsigned pairFunctor = Theory::getTupleConstructor(2);
  unsigned tripleFunctor = Theory::getTupleConstructor(3);

  TermList sSort = s.sugaredExpr();
  TermList tripleSort = tupleSortOf(3, sSort);

  TermStack tripleArgs = { sSort, sSort, sSort,
                           a().sugaredExpr(), a().sugaredExpr(), a().sugaredExpr() };
  Term* triple = Term::create(tripleFunctor, tripleArgs);

  // tuple(Tuple(s,s,s), s, triple, a) : Tuple(Tuple(s,s,s), s) -- a pair whose
  // first component is a triple: the arity to look for is the outer one
  TermStack pairArgs = { tripleSort, sSort, TermList(triple), a().sugaredExpr() };
  Term* pair = Term::create(pairFunctor, pairArgs);

  ASS(Theory::isTupleConstructor(triple));
  ASS(Theory::isTupleConstructor(pair));
}

