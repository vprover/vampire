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
 * @file Factoring.cpp
 * Implements class Factoring.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Ordering.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Factoring.hpp"

static RobSubstitution subst;

namespace Inferences
{

/**
 * Given a pair of literal indices
 * removes the second literal from the clause specified in constructor,
 * applies the substitution, and returns resulting clause.
 * (Also it records this to statistics as factoring.)
 */
Clause *Factoring::attemptFactor(Clause *cl, unsigned i, unsigned j) {
  Literal* l1 = (*cl)[i];
  Literal* l2 = (*cl)[j];

  //we assume there are no duplicate literals
  ASS(l1!=l2);

  if(l1->isEquality())
    //We don't perform factoring with equalities
    return nullptr;

  // check polarity and functor matches
  if(!Literal::headersMatch(l1, l2, false))
    return nullptr;

  const auto &sel = _salg.getLiteralSelector();
  if(sel.isNegativeForSelection(l1)) {
    //We don't perform factoring on negative literals
    // (this check only becomes relevant, when there is more than one literal selected
    // and yet the selected ones are not all positive -- see the check in generateClauses)
    return nullptr;
  }

  subst.reset();
  if(!subst.unify(TermList(l1), 0, TermList(l2), 0))
    return nullptr;

  bool afterCheck = _salg.getOptions().literalMaximalityAftercheck() && _salg.getLiteralSelector().isBGComplete();
  RStack<Literal*> resLits;

  Literal *skipped = l2;

  Literal* skippedAfter = nullptr;
  if (afterCheck && cl->numSelected() > 1) {
    TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

    skippedAfter = subst.apply(skipped, 0);
  }

  const auto &ord = _salg.getOrdering();
  for(unsigned i=0;i<cl->length();i++) {
    Literal* curr=(*cl)[i];
    if(curr!=skipped) {
      Literal* currAfter = subst.apply(curr, 0);

      if (skippedAfter) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

        if (i < cl->numSelected() && ord.compare(currAfter,skippedAfter) == Ordering::GREATER) {
          env.statistics->inferencesBlockedDueToOrderingAftercheck++;
          return nullptr;
        }
      }

      resLits->push(currAfter);
    }
  }

  Clause *genCl = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FACTORING,cl));
  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(genCl, new FactoringExtra(l1, l2));
  return genCl;
}

/**
 * Produces clauses generated from
 * @b premise by the factoring inference rule.
 *
 * Nothing is generated, when the premise contains only one
 * negative literal. Otherwise one of literals used in factoring
 * has to be selected, the other one does not. This deviation from
 * usual factoring rules, where both factored literals have to be
 * selected, is for the sake of incomplete literal selection
 * functions, that select always just one literal. (This would lead
 * to no factoring at all.)
 *
 * If a complete literal selection is used, this makes no difference,
 * as when two literals are unifiable, one cannot be maximal and the
 * other non-maximal in the literal ordering.
 */
void Factoring::generateClauses(Clause *premise, ClauseReceiver receive)
{
  if(premise->length()<=1) {
    return;
  }
  if(premise->numSelected()==1 && _salg.getLiteralSelector().isNegativeForSelection((*premise)[0])) {
    return;
  }

  for(unsigned i = 0; i < premise->numSelected(); i++)
    for(unsigned j = i + 1; j < premise->length(); j++)
      if(Clause *cl = attemptFactor(premise, i, j))
        receive(cl);
}

}
