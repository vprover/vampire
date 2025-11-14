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
  static SynthesisALManager* synthMan = static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance());
  ASS(synthMan);
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    if (lit->isAnswerLiteral() && !synthMan->isComputableOrVar(lit)) {
      return nullptr;
    }
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

LiteralStack collectLiteralsExceptForTwo(Clause* cl, unsigned size, unsigned exception1, unsigned exception2) {
  ASS(size >= cl->length()-2);
  LiteralStack ls(size);
  for (unsigned i = 0; i < cl->length(); ++i) {
    if ((i != exception1) && (i != exception2)) {
      ls.push((*cl)[i]);
    }
  }
  return ls;
}

Option<ClauseIterator> SynthesisAnswerLiteralProcessor::simplifyMany(Clause* cl)
{
  if ((cl->inference().rule() == InferenceRule::ANSWER_LITERAL_JOIN_AS_ITE) ||
      (cl->inference().rule() == InferenceRule::ANSWER_LITERAL_JOIN_WITH_CONSTRAINTS)) {
    // The clause was produced by this very simplification, and it does not need further checking.
    return none<ClauseIterator>();
  }
  // Count the answer literals in the clause.
  unsigned numAnsLits = 0;
  unsigned idx[2];
  for (unsigned i = 0; i < cl->length(); ++i) {
    if ((*cl)[i]->isAnswerLiteral()) {
      if (numAnsLits < 2) {
        idx[numAnsLits] = i;
      }
      numAnsLits++;
      if (numAnsLits > 2) {
        break;
      }
    }
  }
  // This simplification rule deals with clauses with 2 answer literals produced by superposition
  // or resolution (which fill in sythesisExtra).
  // Clauses with a different number of answer literals or prodced by other rules are checked
  // by other simplification rules.
  // TODO: make this work also for:
  // - InferenceRule::UNIT_RESULTING_RESOLUTION
  // - InferenceRule::ALASCA_FOURIER_MOTZKIN
  // - possibly other ALASCA BinInf-based rules
  if (numAnsLits != 2 ||
      ((cl->inference().rule() != InferenceRule::SUPERPOSITION) &&
       (cl->inference().rule() != InferenceRule::RESOLUTION) &&
       (cl->inference().rule() != InferenceRule::CONSTRAINED_RESOLUTION))) {
    return none<ClauseIterator>();
  }

  // Get synthesis information
  SynthesisALManager* synthMan = static_cast<SynthesisALManager*>(SynthesisALManager::getInstance());
  const TwoLiteralInferenceExtra::SynthesisExtra* synExtra = nullptr;
  if (cl->inference().rule() == InferenceRule::SUPERPOSITION) {
    const TwoLiteralRewriteInferenceExtra& extra = env.proofExtra.get<TwoLiteralRewriteInferenceExtra>(cl);
    ASS(extra.selected.otherLiteral->isEquality());
    synExtra = &(extra.selected.synthesisExtra);
  } else if ((cl->inference().rule() == InferenceRule::RESOLUTION) ||
             (cl->inference().rule() == InferenceRule::CONSTRAINED_RESOLUTION)) {
    const TwoLiteralInferenceExtra& extra = env.proofExtra.get<TwoLiteralInferenceExtra>(cl);
    synExtra = &(extra.synthesisExtra);
  }
  ASS(synExtra != nullptr);
  Literal *thenLit = synExtra->thenLit, *elseLit = synExtra->elseLit, *condition = synExtra->condition;
  ASS(condition != nullptr);
  ASS(thenLit != nullptr);
  ASS(elseLit != nullptr);
  ASS_EQ(thenLit->arity(), elseLit->arity());

  // Given the clause `C \/ ans(t) \/ ans(e)`, we join the answer literals in two different ways:
  // 1. using an if-then-else for a stored conditon `cond`, producing:
  //      C \/ ans(if cond then t else e)
  // 2. we use just `ans(t)` and add a constraint on equality of `t` and `e`, producing:
  //      C \/ t!=e \/ ans(t)
  // TODO: if the answer literal has multiple arguments, maybe we should try all combinations
  //       of options 1 and 2 for each argument?
  ClauseStack res;
  // Option 1, using if-then-else, only applies if the two answer literals are different.
  LiteralStack lits = collectLiteralsExceptForTwo(cl, cl->length()-1, idx[0], idx[1]);
  if (thenLit != elseLit) {
    Literal* newAnsLit = synthMan->makeITEAnswerLiteral(condition, thenLit, elseLit);
    lits.push(newAnsLit);
    Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_JOIN_AS_ITE, cl));
    res.push(Clause::fromStack(lits, inf));
    // Remove the answer literal, we reuse the rest below.
    lits.pop();
  }
  // Option 2, using `thenLit` under the condition that the arguments of `thenLit` and `elseLit` are
  // equal, is always applicable.
  synthMan->pushEqualityConstraints(&lits, thenLit, elseLit);
  lits.push(thenLit);
  Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_JOIN_WITH_CONSTRAINTS, cl));
  res.push(Clause::fromStack(lits, inf));

  return some(getPersistentIterator(pvi(ClauseStack::Iterator(res))));
}

}
