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

#include <utility>

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Ordering.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Factoring.hpp"

namespace Inferences
{

/**
 * Return ClauseIterator, that yields clauses generated from
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
ClauseIterator Factoring::generateClauses(Clause* premise)
{
  // bail out before even creating a coroutine frame
  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  if(premise->numSelected()==1 && _salg.getLiteralSelector().isNegativeForSelection((*premise)[0])) {
    return ClauseIterator::getEmpty();
  }

  return pvi(factorings(premise));
}

/**
 * For each unordered pair of literals of @b premise with at least one of them selected,
 * unify them, drop the second, apply the substitution to the rest, and yield the result.
 */
Generator<Clause*> Factoring::factorings(Clause* premise)
{
  LiteralSelector& sel = _salg.getLiteralSelector();
  const Ordering& ord = _salg.getOrdering();
  bool afterCheck = _salg.getOptions().literalMaximalityAftercheck() && sel.isBGComplete();
  unsigned cLen = premise->length();

  RobSubstitution subst;

  for(unsigned fst=0; fst<premise->numSelected(); fst++) {
    Literal* l1 = (*premise)[fst];

    //We don't perform factoring with equalities
    if(l1->isEquality())
      continue;

    //We don't perform factoring on negative literals
    // (this check only becomes relevant, when there is more than one literal selected
    // and yet the selected ones are not all positive -- see the check in generateClauses)
    if(sel.isNegativeForSelection(l1))
      continue;

    for(unsigned snd=fst+1; snd<cLen; snd++) {
      Literal* skipped = (*premise)[snd];

      //we assume there are no duplicate literals
      ASS(l1!=skipped);

      // check polarity and functor matches
      if(!Literal::headersMatch(l1, skipped, false))
        continue;

      subst.reset();
      if(!subst.unify(TermList(l1), 0, TermList(skipped), 0))
        continue;

      Clause* factor;
      {
        RStack<Literal*> resLits;

        Literal* skippedAfter = 0;
        if (afterCheck && premise->numSelected() > 1) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

          skippedAfter = subst.apply(skipped, 0);
        }

        bool blocked = false;
        for(unsigned i=0;i<cLen;i++) {
          Literal* curr=(*premise)[i];
          if(curr!=skipped) {
            Literal* currAfter = subst.apply(curr, 0);

            if (skippedAfter) {
              TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

              if (i < premise->numSelected() && ord.compare(currAfter,skippedAfter) == Ordering::GREATER) {
                env.statistics->inferencesBlockedDueToOrderingAftercheck++;
                blocked = true;
                break;
              }
            }

            resLits->push(currAfter);
          }
        }
        if(blocked)
          continue;

        factor = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FACTORING,premise));
      }

      if(env.options->proofExtra() == Options::ProofExtra::FULL)
        env.proofExtra.insert(factor, new FactoringExtra(l1, skipped));

      co_yield factor;
    }
  }
}

}
