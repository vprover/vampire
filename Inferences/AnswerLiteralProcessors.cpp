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

ClauseIterator AnswerLiteralJoiner::simplifyMany(Clause* cl)
{
  // TODO(hzzv): support also URR
  if ((cl->inference().rule() != InferenceRule::SUPERPOSITION) &&
      (cl->inference().rule() != InferenceRule::RESOLUTION) &&
      (cl->inference().rule() != InferenceRule::CONSTRAINED_RESOLUTION)) {
    return ClauseIterator::getEmpty();
  }
  int numAnsLits = 0;
  unsigned idx[2];
  for (unsigned i = 0; i < cl->length(); ++i) {
    if ((*cl)[i]->isAnswerLiteral()) {
      ASS(numAnsLits < 2);
      idx[numAnsLits] = i;
      numAnsLits++;
    }
  }
  if (numAnsLits < 2) {
    return ClauseIterator::getEmpty();
  }
  ASS_EQ(numAnsLits, 2);
  //std::cout << "performed sup with AL: " << cl->toString() << std::endl;
  //std::cout << "proof extra: " << env.proofExtra.find(cl)->toString() << std::endl;

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
  ASS(synExtra != nullptr);
  ASS(synExtra->condition != nullptr);
  ASS(synExtra->thenLit != nullptr);
  ASS(synExtra->elseLit != nullptr);
  ClauseStack res;
  // We build two options for the joined answer literal.
  // Note: we do not guarantee that the resulting answer literal is computable.
  // That needs to be checked by anoter immediate simplification rule.
  // 1. Unified answer literal:
  RobSubstitution subst;
  bool iteNeeded = false;
  if (subst.unifyArgs(synExtra->thenLit, 0, synExtra->elseLit, 0)) {
    LiteralStack lits(cl->length()-1);
    for (unsigned i = 0; i < cl->length(); ++i) {
      // Apply the substitution on all literals except the answer literals
      if ((i != idx[0]) && (i != idx[1])) {
        Literal* lit = subst.apply((*cl)[i], 0);
        if (lit != (*cl)[i]) {
          iteNeeded = true;
        }
        lits.push(subst.apply((*cl)[i], 0));
      }
    }
    // Add also the unified answer literal
    lits.push(subst.apply(synExtra->thenLit, 0));
    Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_UNIFICATION, cl));
    res.push(Clause::fromStack(lits, inf));
    //std::cout << "unified clause: " << res.top()->toString() << std::endl;
  } else {
    iteNeeded = true;
  }
  // 2. If-then-else answer literal:
  if (iteNeeded) {
    LiteralStack lits(cl->length()-1);
    for (unsigned i = 0; i < cl->length(); ++i) {
      // Apply the substitution on all literals except the answer literals
      if ((i != idx[0]) && (i != idx[1])) {
        lits.push((*cl)[i]);
      }
    }
    // Create the if-then-else literal based on the stored condition
    lits.push(SynthesisALManager::getInstance()->makeITEAnswerLiteral(synExtra->condition, synExtra->thenLit, synExtra->elseLit));
    //std::cout << "ITE literal: " << lits.top()->toString() << std::endl;
    Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_ITE, cl));
    res.push(Clause::fromStack(lits, inf));
    //std::cout << "ITE clause: " << res.top()->toString() << std::endl;
  }

  return getPersistentIterator(pvi(ClauseStack::Iterator(res)));
}

}
