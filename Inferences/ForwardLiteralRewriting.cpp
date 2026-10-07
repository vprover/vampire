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
    // A rewrite rule is oriented at search time between two complementary-variant
    // two-literal clauses C = L | R and D = ~L' | ~R': together they entail
    // L <-> ~R, so a literal Lσ can be replaced by ~Rσ. RewriteRuleIndex keeps
    // one clause of each pair indexed by its rule-side literal and links the
    // two through getCounterpart. Only one clause of the pair is recorded as
    // the premise of the printed inference (the "counterpart" would only add
    // a redundant dependency, see the reductionPremise note in perform()), so
    // replay, which sees only the recorded parents, cannot rebuild the pair.
    // Instead, index the recorded premise itself: every literal of it that
    // could serve as a rule side (i.e. that contains all variables of the
    // other literal, mirroring the containsAllVariablesOf conditions with
    // which RewriteRuleIndex orients its rules) becomes a query target, and
    // perform() below makes the premise its own counterpart.
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
    // Replay queries the private index over the recorded premise instead of
    // the search-time RewriteRuleIndex, and always retrieves complementary
    // generalizations: the recorded premise's rule-side literal has the
    // opposite polarity of the literal it rewrites, whichever of the pair was
    // recorded. During search only negative literals are retrieved
    // complementarily, because the indexed rule sides are always positive.
    auto git = _replayIndex
      ? _replayIndex->getGeneralizations(lit, true)
      : _index->getGeneralizations(lit, lit->isNegative());
    while(git.hasNext()) {
      auto qr = git.next();
      // In replay mode the premise is its own counterpart.
      Clause* counterpart = _replayIndex ? qr.data->clause : _index->getCounterpart(qr.data->clause);

      if(!ColorHelper::compatible(cl->color(), qr.data->clause->color()) ||
         !ColorHelper::compatible(cl->color(), counterpart->color()) ) {
        continue;
      }

      if(cl==qr.data->clause || cl==counterpart) {
  continue;
      }
      
      Literal* rhs0 = (qr.data->literal==(*qr.data->clause)[0]) ? (*qr.data->clause)[1] : (*qr.data->clause)[0];
      // Replay takes the premise's other literal as the replacement unchanged;
      // search-time positive rewrites complement it, as the recorded premise is
      // then the counterpart clause, whose literals have the opposite polarity.
      Literal* rhs = _replayIndex || lit->isNegative() ? rhs0 : Literal::complementaryLiteral(rhs0);
      auto subs = qr.unifier;

      //Due to the way we build the _index, we know that rhs contains only
      //variables present in qr.data->literal
      ASS(qr.data->literal->containsAllVariablesOf(rhs));
      auto rhsS = subs.apply(rhs);

      //The ordering check oriented the rule at search time and guarantees
      //termination of rewriting. Replay does not repeat it: the recorder
      //validates the conclusion against the replayed goal instead, and the
      //ordering may not even be reproducible from the recorded premises.
      if(!_replayIndex && _ord.compare(lit, rhsS)!=Ordering::GREATER) {
  continue;
      }

      // In replay mode the recorded premise is also the premise of the
      // certificate; search-time positive rewrites record the counterpart.
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
        // Replay runs this engine only on the recorded parents, and
        // _replayIndex restricts matches to the recorded premise itself, so
        // the first candidate is the recorded inference. The recorder stores
        // the certificate only when the conclusion reproduces the replayed
        // goal (isSameAsProofStep); a miss needs no retry and is detected
        // by the replayer through getLastRecordedInferenceInformation().
        Shell::InferenceRecorder::instance()->replayedInference(
            replacement, {cl, premise}, substitutions,
            Shell::InferenceRecorder::InferenceInformation::LiteralPositionKind::RESOLVED,
            {{0, i}, {1, premise->getLiteralPosition(qr.data->literal)}});
      }
      return true;
    }
  }

  return false;
}

};
