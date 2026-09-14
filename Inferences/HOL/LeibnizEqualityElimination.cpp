/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LeibnizEqualityElimination.cpp
 * Implements class LeibnizEqualityElimination.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "LeibnizEqualityElimination.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

namespace {

struct LeibnizEqualityRecord {
  unsigned var;
  TermList argSort;
  TermList arg;
};

bool polarity(Literal* lit)
{
  auto [lhs, rhs] = lit->eqArgs();
  ASS(HOL::isBool(lhs)  || HOL::isBool(rhs));
  if (HOL::isBool(lhs)) {
    return lit->polarity() == HOL::isTrue(lhs);
  }
  return lit->polarity() == HOL::isTrue(rhs);
}

LeibnizEqualityRecord getLiteralInfo(Literal* lit)
{
  auto [lhs, rhs] = lit->eqArgs();
  TermList nonBooleanSide = HOL::isBool(rhs) ? lhs : rhs;
  ASS(nonBooleanSide.isTerm());
  Term* term = nonBooleanSide.term();

  LeibnizEqualityRecord ler;
  ler.var = term->nthArgument(2)->var();
  ler.arg = *term->nthArgument(3);
  ler.argSort = *term->nthArgument(0);

  return ler;
}

bool isPair(Literal* l1, Literal* l2)
{
  ASS_NEQ(polarity(l1), polarity(l2));

  LeibnizEqualityRecord ler1 = getLiteralInfo(l1);
  LeibnizEqualityRecord ler2 = getLiteralInfo(l2);
  return ler1.var == ler2.var;
}

Clause* createConclusion(Clause* premise, Literal* newLit, Literal* posLit, Literal* negLit, RobSubstitution& subst)
{
  RStack<Literal*> resLits;
  resLits->push(subst.apply(newLit, 0));
  for (const auto& curr : *premise) {
    if (curr != posLit && curr != negLit) {
      resLits->push(subst.apply(curr, 0));
    }
  }
  return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::LEIBNIZ_ELIMINATION, premise));
}

}

ClauseIterator LeibnizEqualityElimination::generateClauses(Clause* premise)
{
  static TermStack args;
  TermList head;

  LiteralStack positiveLits;
  LiteralStack negativeLits;

  Literal* posLit;
  Literal* negLit;

  for (const auto& lit : *premise){
    auto [lhs, rhs] = lit->eqArgs();
    if (!HOL::isBool(lhs) && !HOL::isBool(rhs)) {
      continue;
    }
    TermList nonBooleanSide = HOL::isBool(rhs) ? lhs : rhs;

    auto head = HOL::getHeadAndArgs(nonBooleanSide, args);
    if (!head.isVar() || args.size() != 1) {
      continue;
    }

    bool pol = polarity(lit);
    const LiteralStack& lits = pol ? negativeLits : positiveLits;
    for (const auto& lit2 : lits) {
      if (isPair(lit, lit2)) {
        posLit = pol ? lit : lit2;
        negLit = pol ? lit2 : lit;
        goto afterLoop;
      }
    }
    if (pol) {
      positiveLits.push(lit);
    } else {
      negativeLits.push(lit);
    }
  }
  return ClauseIterator::getEmpty();

afterLoop:

  ClauseStack clauses;
  static RobSubstitution subst;
  subst.reset();

  auto lerPosLit = getLiteralInfo(posLit);
  auto lerNegLit = getLiteralInfo(negLit);
  auto argS = lerNegLit.argSort;

  auto newLit = Literal::createEquality(true, lerPosLit.arg, lerNegLit.arg, argS);

  auto var = TermList::var(lerPosLit.var);

  using namespace HOL::create;

  TermList vEquals = equality(argS);
  // creating the term = arg (which is eta-equivalent to λx. arg = x)
  TermList t1 = HOL::create::app(vEquals, lerNegLit.arg);
  if (subst.unify(var, 0, t1, 0)) {
    clauses.push(createConclusion(premise, newLit, posLit, negLit, subst));
    subst.reset();
  }

  TermList db = HOL::getDeBruijnIndex(0, argS);
  // creating the term λx. arg != x
  TermList t2 = namelessLambda(argS, app(neg(), app(vEquals, {lerPosLit.arg,db})));
  if (subst.unify(var, 0, t2, 0)) {
    clauses.push(createConclusion(premise, newLit, posLit, negLit, subst));
  }

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(clauses)));
}

}
