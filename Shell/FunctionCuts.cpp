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
 * @file FunctionCuts.cpp
 */

#include "FunctionCuts.hpp"

#include "Lib/List.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

namespace Shell {

using namespace Kernel;

void FunctionCuts::apply(Problem &prb)
{
  CALL("FunctionCuts::apply")

  UnitList::Iterator units(prb.units());

  DHSet<unsigned> candidates;
  while(units.hasNext()) {
    Unit *unit = units.next();
    if(!unit->isClause())
      continue;

    Clause *cl = unit->asClause();
    for(unsigned i = 0; i < cl->length(); i++) {
      NonVariableNonTypeIterator subterms((*cl)[i]);
      while(subterms.hasNext())
        candidates.insert(subterms.next().term()->functor());
    }
  }

  decltype(candidates)::Iterator functors(candidates);
  Inference inference((FromInput(UnitInputType::AXIOM)));
  TermList x(0, false);
  TermList y(1, false);

  while(functors.hasNext()) {
    unsigned functor = functors.next();
    Signature::Symbol *function = env.signature->getFunction(functor);
    // TODO polymorphism
    if(function->numTypeArguments() != 0 || function->numTermArguments() != 2 || function->interpreted())
      continue;

    OperatorType *fnType = function->fnType();
    TermList sort = fnType->arg(0);
    if(sort != fnType->arg(1))
      continue;

    OperatorType *constType = OperatorType::getConstantsType(sort);
    unsigned sk1 = env.signature->addSkolemFunction(0);
    env.signature->getFunction(sk1)->setType(constType);
    Term *sk1t = Term::createConstant(sk1);
    unsigned sk2 = env.signature->addSkolemFunction(0);
    env.signature->getFunction(sk2)->setType(constType);
    Term *sk2t = Term::createConstant(sk2);

    Term *plhs = Term::create(functor, {x, y});
    Term *prhs = Term::create(functor, {y, x});
    Term *nlhs = Term::create(functor, {TermList(sk1t), TermList(sk2t)});
    Term *nrhs = Term::create(functor, {TermList(sk2t), TermList(sk1t)});
    Literal *plit = Literal::createEquality(true, TermList(plhs), TermList(prhs), sort);
    Literal *nlit = Literal::createEquality(false, TermList(nlhs), TermList(nrhs), sort);

    unsigned sp1 = env.signature->addFreshPredicate(0, "$$commutative");
    unsigned sp2 = env.signature->addFreshPredicate(0, "$$commutative");
    Literal *plabel = Literal::create(sp1, true, {});
    Literal *nlabel = Literal::create(sp2, true, {});

    Clause *pdef = new (2) Clause(2, inference);
    (*pdef)[0] = Literal::complementaryLiteral(plabel);
    (*pdef)[1] = plit;

    Clause *ndef = new (2) Clause(2, inference);
    (*ndef)[0] = Literal::complementaryLiteral(nlabel);
    (*ndef)[1] = nlit;

    Clause *split = new(2) Clause(2, inference);
    (*split)[0] = plabel;
    (*split)[1] = nlabel;

    UnitList *list = UnitList::singleton(pdef);
    list = UnitList::cons(ndef, list);
    list = UnitList::cons(split, list);
    prb.addUnits(list);
  }
}

}