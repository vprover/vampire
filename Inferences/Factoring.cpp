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
 * This functor given a pair of literal indices
 * removes the second literal from the clause specified in constructor,
 * applies the substitution, and returns resulting clause.
 * (Also it records this to statistics as factoring.)
 */
class Factoring::ResultsFn
{
public:
  ResultsFn(Clause* cl, bool afterCheck, LiteralSelector &sel, Ordering& ord)
  : _cl(cl), _cLen(cl->length()), _afterCheck(afterCheck), _sel(sel), _ord(ord) {}
  Clause* operator() (std::pair<unsigned,unsigned> nums)
  {
    Literal* l1 = (*_cl)[nums.first];
    Literal* l2 = (*_cl)[nums.second];

    //we assume there are no duplicate literals
    ASS(l1!=l2);

    if(l1->isEquality())
      //We don't perform factoring with equalities
      return nullptr;

    // check polarity and functor matches
    if(!Literal::headersMatch(l1, l2, false))
      return nullptr;

    if(_sel.isNegativeForSelection(l1)) {
      //We don't perform factoring on negative literals
      // (this check only becomes relevant, when there is more than one literal selected
      // and yet the selected ones are not all positive -- see the check in generateClauses)
      return nullptr;
    }

    subst.reset();
    if(!subst.unify(TermList(l1), 0, TermList(l2), 0))
      return nullptr;

    RStack<Literal*> resLits;

    Literal *skipped = l2;

    Literal* skippedAfter = 0;
    if (_afterCheck && _cl->numSelected() > 1) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

      skippedAfter = subst.apply(skipped, 0);
    }

    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=skipped) {
        Literal* currAfter = subst.apply(curr, 0);

        if (skippedAfter) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

          if (i < _cl->numSelected() && _ord.compare(currAfter,skippedAfter) == Ordering::GREATER) {
            env.statistics->inferencesBlockedDueToOrderingAftercheck++;
            return nullptr;
          }
        }

        resLits->push(currAfter);
      }
    }

    Clause *cl = Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FACTORING,_cl));
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(cl, new FactoringExtra(l1, l2));
    return cl;
  }
private:
  static RobSubstitution subst;
  Clause* _cl;
  ///length of the premise clause
  unsigned _cLen;
  bool _afterCheck;
  LiteralSelector& _sel;
  Ordering& _ord;
};
RobSubstitution Factoring::ResultsFn::subst;

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
  if(premise->length()<=1) {
    return ClauseIterator::getEmpty();
  }
  if(premise->numSelected()==1 && _salg->getLiteralSelector().isNegativeForSelection((*premise)[0])) {
    return ClauseIterator::getEmpty();
  }

  auto it1 = getCombinationIterator(0u,premise->numSelected(),premise->length());

  auto it2 = getMappingIterator(it1,ResultsFn(premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      _salg->getLiteralSelector(), _salg->getOrdering()));

  auto it3 = getFilteredIterator(it2, NonzeroFn());

  return pvi( it3 );
}

}
