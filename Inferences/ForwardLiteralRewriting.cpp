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

#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "ForwardLiteralRewriting.hpp"
#include "Shell/InferenceRecorder.hpp"

namespace Inferences
{

ForwardLiteralRewriting::ForwardLiteralRewriting(SaturationAlgorithm& salg, Clause* replayPremise)
  : _ord(salg.getOrdering()),
    _index(salg.getSimplifyingIndex<RewriteRuleIndex>())
{
  if (replayPremise) {
    ASS(env.reconstruction);
    // The proof contains the resolving premise, but omits the complementary
    // clause used to orient the rewrite rule during search.
    _replayIndex = std::make_unique<CodeTreeLIS<LiteralClause>>();
    if (replayPremise->length() == 2) {
      for (unsigned i = 0; i < 2; ++i) {
        if ((*replayPremise)[i]->containsAllVariablesOf((*replayPremise)[1 - i])) {
          _replayIndex->handle(LiteralClause{(*replayPremise)[i], replayPremise}, true);
        }
      }
    }
  }
}

bool ForwardLiteralRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  TIME_TRACE("forward literal rewriting");

  unsigned clen=cl->length();

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    auto git = _replayIndex
      ? _replayIndex->getGeneralizations(lit, true)
      : _index->getGeneralizations(lit, lit->isNegative());
    while(git.hasNext()) {
      auto qr = git.next();
      Clause* counterpart = _replayIndex ? qr.data->clause : _index->getCounterpart(qr.data->clause);

      if(!ColorHelper::compatible(cl->color(), qr.data->clause->color()) ||
         !ColorHelper::compatible(cl->color(), counterpart->color()) ) {
        continue;
      }

      if(cl==qr.data->clause || cl==counterpart) {
  continue;
      }
      
      Literal* rhs0 = (qr.data->literal==(*qr.data->clause)[0]) ? (*qr.data->clause)[1] : (*qr.data->clause)[0];
      Literal* rhs = _replayIndex || lit->isNegative() ? rhs0 : Literal::complementaryLiteral(rhs0);
      auto subs = qr.unifier;

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.data->literal
      ASS(qr.data->literal->containsAllVariablesOf(rhs));
      auto rhsS = subs.apply(rhs);

      if(!_replayIndex && _ord.compare(lit, rhsS)!=Ordering::GREATER) {
  continue;
      }

      Clause* premise=_replayIndex || lit->isNegative() ? qr.data->clause : counterpart;
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

      premises = pvi( getSingletonIterator(premise));
      replacement = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, cl, premise));
      if (env.reconstruction) {
        std::vector<Substitution> substitutions(2);
        auto variables = premise->getVariableIterator();
        while (variables.hasNext()) {
          unsigned variable = variables.next();
          substitutions[1].bind(variable, subs.apply(TermList::var(variable)));
        }
        if (!Shell::InferenceRecorder::instance()->replayedInference(
              replacement, {cl, premise}, substitutions,
              Shell::InferenceRecorder::InferenceInformation::LiteralPositionKind::RESOLVED,
              {{0, i}, {1, premise->getLiteralPosition(qr.data->literal)}})) {
          replacement->destroy();
          replacement = nullptr;
          continue;
        }
      }
      return true;
    }
  }

  return false;
}

};
