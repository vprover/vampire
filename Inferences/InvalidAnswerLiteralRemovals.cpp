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
 * @file InvalidAnswerLiteralRemovals.cpp
 * Implements classes UncomputableAnswerLiteralRemoval and UndesiredAnswerLiteralRemoval.
 */

#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/AnswerLiteralManager.hpp"

#include "InvalidAnswerLiteralRemovals.hpp"

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
  // TODO(hzzv): start simple, only trigger for Sup:
  if (cl->inference().rule() != InferenceRule::SUPERPOSITION) {
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

  const TwoLiteralRewriteInferenceExtra* se = static_cast<const TwoLiteralRewriteInferenceExtra*>(env.proofExtra.find(cl));
  ASS(se != nullptr);
  ASS(se->selected.otherLiteral->isEquality());
  ClauseStack res;
  // We build two options for the joined answer literal.
  // Note: we do not guarantee that the resulting answer literal is computable.
  // That needs to be checked by anoter immediate simplification rule.
  // 1. Unified answer literal:
  RobSubstitution subst;
  bool iteNeeded = false;
  if (subst.unifyArgs((*cl)[idx[0]], 0, (*cl)[idx[1]], 0)) {
    LiteralStack lits(cl->length()-1);
    for (unsigned i = 0; i < cl->length(); ++i) {
      // Apply the substitution on all literals except one of the answer literals
      if (i != idx[0]) {
        Literal* lit = subst.apply((*cl)[i], 0);
        if (lit != (*cl)[i]) {
          iteNeeded = true;
        }
        lits.push(subst.apply((*cl)[i], 0));
      }
    }
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
    lits.push(SynthesisALManager::getInstance()->makeITEAnswerLiteral(se->selected.conditionLiteral, (*cl)[idx[0]], (*cl)[idx[1]]));
    //std::cout << "ITE literal: " << lits.top()->toString() << std::endl;
    Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_ITE, cl));
    res.push(Clause::fromStack(lits, inf));
    //std::cout << "ITE clause: " << res.top()->toString() << std::endl;
  }

  return getPersistentIterator(pvi(ClauseStack::Iterator(res)));
}

}
