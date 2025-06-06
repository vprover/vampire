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
 * @file AnswerLiteralProcessors.cpp
 * Implements classes UncomputableAnswerLiteralRemoval and UndesiredAnswerLiteralRemoval.
 */

#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/TermIterators.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/AnswerLiteralManager.hpp"

#include "AnswerLiteralProcessors.hpp"

namespace Inferences
{

Clause* UncomputableAnswerLiteralRemoval::simplify(Clause* cl)
{
  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral() && !lit->computableOrVar())
      return nullptr;
  }
  return cl;
}

Clause* MultipleAnswerLiteralRemoval::simplify(Clause* cl)
{
  unsigned cLen = cl->length();
  bool found = false;
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral()) {
      if (found) {
        return nullptr;
      } else {
        found = true;
      }
    }
  }
  return cl;
}

UndesiredAnswerLiteralRemoval::UndesiredAnswerLiteralRemoval(const std::string& avoidThese)
{
  Formula* top_fla = static_cast<FormulaUnit*>(Parse::TPTP::parseFormulaFromString(avoidThese))->formula();
  Formula* fla = top_fla;

  while (fla->connective() == FORALL || fla->connective() == EXISTS) {
    fla = fla->qarg();
  }
  if (fla->connective() != OR && fla->connective() != LITERAL) {
    goto error;
  }

  {
    Stack<Literal*> disjuncts;
    if (fla->connective() == LITERAL) {
      disjuncts.push(fla->literal());
    } else {
      FormulaList* args = fla->args();
      while (args) {
        auto arg = args->head();
        if (arg->connective() != LITERAL)
          goto error;
        disjuncts.push(arg->literal());
        args = args->tail();
      }
    }

    _avoiders = Clause::fromStack(disjuncts,Inference(NonspecificInference0(UnitInputType::ASSUMPTION,InferenceRule::INPUT)));

    return;
  }

  error:
    USER_ERROR("Invalid format of the question avoider formula: "+top_fla->toString());
}

Clause* UndesiredAnswerLiteralRemoval::simplify(Clause* cl)
{
  static RobSubstitution helperSubst;

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral() && lit->isNegative()) {
      for (Literal* toAvoid : _avoiders->iterLits()) {
        if (lit->functor() == toAvoid->functor()) {
          helperSubst.reset();
          if (helperSubst.matchArgs(toAvoid,0,lit,1)) {
            return nullptr;
          }
        }
      }
    }
  }

  return cl;
}

Clause* SynthesisAnswerLiteralProcessor::simplify(Clause* cl)
{
  if ((cl->inference().rule() == InferenceRule::ANSWER_LITERAL_ITE) ||
      (cl->inference().rule() == InferenceRule::ANSWER_LITERAL_UNIFICATION)) {
    // The clause was produced by this very simplification, and it does not need further checking.
    return cl;
  }
  // Count the answer literals in the clause.
  int numAnsLits = 0;
  unsigned idx[2];
  for (unsigned i = 0; i < cl->length(); ++i) {
    if ((*cl)[i]->isAnswerLiteral()) {
      ASS(numAnsLits < 2);
      idx[numAnsLits] = i;
      numAnsLits++;
    }
  }
  // Clause with 0 answer literals is okay,
  // clause with 3+ answer literals is not okay,
  // clause with 1 answer literal is okay only if the answer literal is computable,
  // and we deal with clause with 2 answer literals below.
  if (numAnsLits == 0) {
    return cl;
  } else if (numAnsLits == 3) {
    return nullptr;
  }
  SynthesisALManager* synthMan = static_cast<SynthesisALManager*>(SynthesisALManager::getInstance());
  if (numAnsLits == 1) {
    if (!(*cl)[idx[0]]->computableOrVar()) {
      RobSubstitution subst;
      Literal* newAnsLit = synthMan->selfUnifyToRemoveUncomputableConditions((*cl)[idx[0]], &subst);
      if (newAnsLit) {
        LiteralStack lits(cl->length());
        for (unsigned i = 0; i < cl->length(); ++i) {
          // Apply the substitution on all literals except the answer literal
          if (i != idx[0]) {
            lits.push(subst.apply((*cl)[i], 0));
          }
        }
        // Add the unified answer literal
        lits.push(newAnsLit);
        ASS(lits.top()->computableOrVar());
        Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_UNIFICATION, cl));
        return Clause::fromStack(lits, inf);
      } else {
        return nullptr;
      }
    }
    return cl;
  }
  // If a clause has 2 answer literals, for some inference rules (which fill synthesisExtra),
  // we can join the answer literals into 1.
  if ((cl->inference().rule() != InferenceRule::SUPERPOSITION) &&
      (cl->inference().rule() != InferenceRule::RESOLUTION) &&
      (cl->inference().rule() != InferenceRule::CONSTRAINED_RESOLUTION)) {
    // TODO(hzzv): support also URR
    return nullptr;
  }

  // Get synthesis information
  const TwoLiteralInferenceExtra::SynthesisExtra* synExtra = nullptr;
  if (cl->inference().rule() == InferenceRule::SUPERPOSITION) {
    const TwoLiteralRewriteInferenceExtra* extra = static_cast<const TwoLiteralRewriteInferenceExtra*>(env.proofExtra.find(cl));
    ASS(extra != nullptr);
    ASS(extra->selected.otherLiteral->isEquality());
    synExtra = &(extra->selected.synthesisExtra);
  } else if ((cl->inference().rule() == InferenceRule::RESOLUTION) ||
             (cl->inference().rule() == InferenceRule::CONSTRAINED_RESOLUTION)) {
    const TwoLiteralInferenceExtra* extra = static_cast<const TwoLiteralInferenceExtra*>(env.proofExtra.find(cl));
    ASS(extra != nullptr);
    synExtra = &(extra->synthesisExtra);
  }
  Literal *thenLit = synExtra->thenLit, *elseLit = synExtra->elseLit;
  ASS(synExtra != nullptr);
  ASS(synExtra->condition != nullptr);
  ASS(thenLit != nullptr);
  ASS(elseLit != nullptr);
  ASS_EQ(thenLit->arity(), elseLit->arity());

  // If either of the answer literals is uncomputable, try to make it computable.
  // TODO(hzzv): can the structure be simplified? Write it properly down and check.
  // Maybe we can first construct the new ite-AL,
  // and then if that is uncomputable, try to make that computable??
  RobSubstitution subst;
  if (!thenLit->computableOrVar()) {
    thenLit = synthMan->selfUnifyToRemoveUncomputableConditions(thenLit, &subst);
    if (!thenLit) {
      return nullptr;
    }
    elseLit = subst.apply(elseLit, 0);
  }
  if (!elseLit->computableOrVar()) {
    elseLit = synthMan->selfUnifyToRemoveUncomputableConditions(elseLit, &subst);
    if (!elseLit) {
      return nullptr;
    }
    thenLit = subst.apply(thenLit, 0);
  }
  ASS(thenLit->computableOrVar());
  ASS(elseLit->computableOrVar());

  // We will try to join `thenLit` and `elseLit`.
  // We assume that which symbols are uncomputable is the same for all answer literal arguments.
  // Let "thenLit = ~ans(t1, ..., tN)" and "elseLit = ~ans(e1, ..., eN)".
  // We might have already used `subst` to make these two literals computable.
  // Thus, we compute `condition = (synExtra->condition)subst`, then:
  // - if `condition` is computable, then the joined answer literal is:
  //    ~ans(ite(condition, t1, e1), ..., ite(condition, tN, eN)),
  // - else if `M = mgu(thenLit, elseLit)`, then the joined answer literal is:
  //    (thenLit)M,
  // - otherwise we cannot join the answer literal, and so we fail and return nullptr.
  // If we computed the joined answer literal, we also apply `subst` (and possibly `M`)
  // on all the other non-answer literals in the clause.
  // TODO(hzzv): make this work for different arguments admitting different (un)computable symbols.
  Literal* newAnsLit = nullptr;
  Literal* condition = subst.apply(synExtra->condition, 0);
  InferenceRule rule;
  if (condition->computableOrVar()) {
    // Condition is computable, join the answer literals using if-then-else
    newAnsLit = synthMan->makeITEAnswerLiteral(condition, thenLit, elseLit);
    rule = InferenceRule::ANSWER_LITERAL_ITE;
  } else {
    // Condition is not computable, try unifying the two answer literals.
    // We reuse and extend `subst`.
    newAnsLit = synthMan->unifyConsideringITE(&subst, thenLit, elseLit);
    rule = InferenceRule::ANSWER_LITERAL_UNIFICATION;
  }
  if (newAnsLit) {
    ASS(newAnsLit->computableOrVar());
    // New answer literal was constructed.
    // Copy over all other literals, apply on them the substitution,
    // and add the new answer literal.
    LiteralStack lits(cl->length()-1);
    for (unsigned i = 0; i < cl->length(); ++i) {
      if ((i != idx[0]) && (i != idx[1])) {
        lits.push(subst.apply((*cl)[i], 0));
      }
    }
    lits.push(newAnsLit);
    Inference inf(SimplifyingInference1(rule, cl));
    return Clause::fromStack(lits, inf);
  }
  // The answer literals cannot be joined.
  return nullptr;
}

}
