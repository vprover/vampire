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

void ForwardLiteralRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("ForwardLiteralRewriting::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<RewriteRuleIndex*>(
    _salg->getIndexManager()->request(REWRITE_RULE_SUBST_TREE) );
}

void ForwardLiteralRewriting::detach()
{
  CALL("ForwardLiteralRewriting::detach");
  _index=0;
  _salg->getIndexManager()->release(REWRITE_RULE_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


bool ForwardLiteralRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("ForwardLiteralRewriting::perform");

  Ordering& ordering = _salg->getOrdering();

  TimeCounter tc(TC_FORWARD_LITERAL_REWRITING);

  unsigned clen=cl->length();

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    SLQueryResultIterator git=_index->getGeneralizations(lit, lit->isNegative(), true);
    while(git.hasNext()) {
      SLQueryResult qr=git.next();
      Clause* counterpart=_index->getCounterpart(qr.clause);

      if(!ColorHelper::compatible(cl->color(), qr.clause->color()) ||
         !ColorHelper::compatible(cl->color(), counterpart->color()) ) {
        continue;
      }

      if(cl==qr.clause || cl==counterpart) {
  continue;
      }
      
      Literal* rhs0 = (qr.literal==(*qr.clause)[0]) ? (*qr.clause)[1] : (*qr.clause)[0];
      Literal* rhs = lit->isNegative() ? rhs0 : Literal::complementaryLiteral(rhs0);

      ASS(qr.substitution->isIdentityOnQueryWhenResultBound());

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.literal
      ASS(qr.literal->containsAllVariablesOf(rhs));
      Literal* rhsS=qr.substitution->applyToBoundResult(rhs);

      if(ordering.compare(lit, rhsS)!=Ordering::GREATER) {
  continue;
      }

      Clause* premise=lit->isNegative() ? qr.clause : counterpart;
      // Martin: reductionPremise does not justify soundness of the inference
      //  (and brings in extra dependency which confuses splitter).
      //  Is there any other use for it?
      // TODO - reductionPremise is required for proof construction only,
      //        it should be included in some kind of Inference object. Consider this
      //        when reviewing proof construction
      /*
      Clause* reductionPremise=lit->isNegative() ? counterpart : qr.clause;
      if(reductionPremise==premise) {
  reductionPremise=0;
      }
      */

      Clause* res = new(clen) Clause(clen, SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, cl, premise));

      (*res)[0]=rhsS;

      unsigned next=1;
      for(unsigned i=0;i<clen;i++) {
  Literal* curr=(*cl)[i];
  if(curr!=lit) {
    (*res)[next++] = curr;
  }
      }
      ASS_EQ(next,clen);

      env.statistics->forwardLiteralRewrites++;

      premises = pvi( getSingletonIterator(premise));
      replacement = res;
      return true;
    }
  }

  return false;
}

};
