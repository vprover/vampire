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
 * @file ForwardLiteralRewriting.cpp
 * Implements class ForwardLiteralRewriting.
 */

#include "Lib/Int.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "ForwardLiteralRewriting.hpp"

namespace Inferences
{

using namespace Lib;

void ForwardLiteralRewriting::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<RewriteRuleIndex*>(
    _salg->getIndexManager()->request(REWRITE_RULE_SUBST_TREE) );
}

void ForwardLiteralRewriting::detach()
{
  _index=0;
  _salg->getIndexManager()->release(REWRITE_RULE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


bool ForwardLiteralRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  TIME_TRACE("forward literal rewriting");

  unsigned clen=cl->length();

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    auto git = _index->getGeneralizations(lit, lit->isNegative(), true);
    while(git.hasNext()) {
      auto qr = git.next();
      Clause* counterpart=_index->getCounterpart(qr.data->clause);

      if(!ColorHelper::compatible(cl->color(), qr.data->clause->color()) ||
         !ColorHelper::compatible(cl->color(), counterpart->color()) ) {
        continue;
      }

      if(cl==qr.data->clause || cl==counterpart) {
  continue;
      }
      
      Literal* rhs0 = (qr.data->literal==(*qr.data->clause)[0]) ? (*qr.data->clause)[1] : (*qr.data->clause)[0];
      Literal* rhs = lit->isNegative() ? rhs0 : Literal::complementaryLiteral(rhs0);
      auto subs = qr.unifier;

      ASS(subs->isIdentityOnQueryWhenResultBound());

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.data->literal
      ASS(qr.data->literal->containsAllVariablesOf(rhs));
      Literal* rhsS = subs->applyToBoundResult(rhs);

      if(ordering.compare(lit, rhsS)!=Ordering::GREATER) {
  continue;
      }

      Clause* premise=lit->isNegative() ? qr.data->clause : counterpart;
      // Martin: reductionPremise does not justify soundness of the inference
      //  (and brings in extra dependency which confuses splitter).
      //  Is there any other use for it?
      // TODO - reductionPremise is required for proof construction only,
      //        it should be included in some kind of Inference object. Consider this
      //        when reviewing proof construction
      /*
      Clause* reductionPremise=lit->isNegative() ? counterpart : qr.data->clause;
      if(reductionPremise==premise) {
  reductionPremise=0;
      }
      */

      RStack<Literal*> resLits;

      resLits->push(rhsS);

      for(Literal* curr : cl->iterLits()) {
        if(curr!=lit) {
          resLits->push(curr);
        }
      }

      env.statistics->forwardLiteralRewrites++;

      premises = pvi( getSingletonIterator(premise));
      replacement = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, cl, premise));
      return true;
    }
  }

  return false;
}

};
