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

bool SynthesisAnswerLiteralProcessor::unifyTermWithBothBranches(RobSubstitution* subst, TermList& t, TermList& branch1, TermList& branch2, TermList& res) {
  TermList r;
  if (!unifyWithITE(subst, branch1, t, r) || !unifyWithITE(subst, branch2, r, res)) {
    return false;
  }
  return true;
}

bool SynthesisAnswerLiteralProcessor::unifyWithITE(RobSubstitution* subst, TermList& t1, TermList& t2, TermList& res) {
  if (subst->unify(t1, 0, t2, 0)) {
    res = subst->apply(t1, 0);
    return true;
  }
  SynthesisALManager* synthMan = static_cast<SynthesisALManager*>(SynthesisALManager::getInstance());
  if (synthMan->isITE(t1)) {
    if (synthMan->isITE(t2)) {
      // Both terms to unify are if-then-elses.
      // Their then-branches and their else-branches must be unifiable separately into r1, r2; and:
      // - either their conditions must be unifiable,
      // - or r1 and r2 must be unifiable.
      // Check the conditions:
      TermList cond1 = *t1.term()->nthArgument(0), cond2 = *t2.term()->nthArgument(0);
      if (cond1.term()->functor() != cond2.term()->functor()) {
        return false;
      }
      bool allShouldUnify = true;
      if (subst->unifyArgs(cond1.term(), 0, cond2.term(), 0)) {
        allShouldUnify = false;
      }
      // Unify the branches separately:
      TermList r1, r2;
      if (!unifyWithITE(subst, *t1.term()->nthArgument(1), *t2.term()->nthArgument(1), r1) ||
          !unifyWithITE(subst, *t1.term()->nthArgument(2), *t2.term()->nthArgument(2), r2)) {
        return false;
      }
      if (allShouldUnify) {
        // Unify the two branches together:
        if (!unifyWithITE(subst, r1, r2, res)) {
          return false;
        }
        return true;
      } else {
        // Create a new if-then-else:
        Term* cond = subst->apply(cond1, 0).term();
        res = TermList(synthMan->createRegularITE(cond, r1, r2, env.signature->getFunction(t1.term()->functor())->fnType()->result()));
        return true;
      }
    } else {
      // t2 is not an if-then-else. That means it must unify with both branches of t1.
      return unifyTermWithBothBranches(subst, t2, *t1.term()->nthArgument(1), *t1.term()->nthArgument(2), res);
    }
  } else if (synthMan->isITE(t2)) {
    // Case symmetric to the one just above: t1 must unify with both branches of t2.
    return unifyTermWithBothBranches(subst, t1, *t2.term()->nthArgument(1), *t2.term()->nthArgument(2), res);
  } else {
    return false;
  }
}

Literal* SynthesisAnswerLiteralProcessor::unifyWithITE(RobSubstitution* subst, Literal* l1, Literal* l2) {
  ASS_EQ(l1->functor(), l2->functor());
  if (subst->unifyArgs(l1, 0, l2, 0)) {
    return subst->apply(l1, 0);
  }
  Stack<TermList> args;
  for (unsigned i = 0; i < l1->arity(); ++i) {
    TermList arg;
    if (!unifyWithITE(subst, *l1->nthArgument(i), *l2->nthArgument(i), arg)) {
      return nullptr;
    }
    args.push(arg);
  }
  Stack<TermList>::RefIterator it(args);
  while (it.hasNext()) {
    TermList& arg = it.next();
    TermList argSub = subst->apply(arg, 0);
    if (arg != argSub) {
      it.replace(argSub);
    }
  }
  return Literal::create(l1->functor(), l1->arity(), l1->polarity(), args.begin());
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
  // clause with 1 answer literal is okay only if the answer literal is computable,
  // clause with 3+ answer literals is not okay.
  if (numAnsLits == 0) {
    return cl;
  } else if (numAnsLits == 1) {
    if (!(*cl)[idx[0]]->computableOrVar()) {
      return nullptr;
    }
    return cl;
  } else if (numAnsLits == 3) {
    return nullptr;
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
  ASS(synExtra != nullptr);
  ASS(synExtra->condition != nullptr);
  ASS(synExtra->thenLit != nullptr);
  ASS(synExtra->elseLit != nullptr);
  if (!synExtra->thenLit->computableOrVar() || ! synExtra->elseLit->computableOrVar()) {
    // We cannot make a computable answer literal from an uncomputable one
    // (not even if the other answer literal is computable).
    return nullptr;
  }
  ASS_EQ(synExtra->thenLit->arity(), synExtra->elseLit->arity());

  // We will try to join thenLit and elseLit.
  // We assume that which symbols are uncomputable is the same for all answer literal arguments.
  // Thus, with "thenLit = ~ans(t1, ..., tN)" and "elseLit = ~ans(e1, ..., eN)":
  // - if condition is computable, then the joined answer literal is:
  //    ~ans(ite(condition, t1, e1), ..., ite(condition, tN, eN)),
  // - else if thenLit and elseLit are unifiable by an mgu M, then the joined answer literal
  //   is (thenLit)M, and we also apply M on all the other non-answer literals in the clause,
  // - otherwise we cannot join the answer literal, and so we fail and return nullptr.
  // TODO(hzzv): make this work for different arguments admitting different (un)computable symbols.
  Clause* replacement = nullptr;
  if (synExtra->condition->computableOrVar()) {
    // Condition is computable, join the answer literals using if-then-else
    LiteralStack lits(cl->length()-1);
    for (unsigned i = 0; i < cl->length(); ++i) {
      // Copy over all literals except for the answer literals
      if ((i != idx[0]) && (i != idx[1])) {
        lits.push((*cl)[i]);
      }
    }
    // Create the if-then-else literal based on the stored condition
    lits.push(SynthesisALManager::getInstance()->makeITEAnswerLiteral(synExtra->condition, synExtra->thenLit, synExtra->elseLit));
    ASS(lits.top()->computableOrVar());
    Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_ITE, cl));
    replacement = Clause::fromStack(lits, inf);
  } else {
    // Condition is not computable, try unifying the two answer literals
    RobSubstitution subst;
    Literal* resAnsLit = unifyWithITE(&subst, synExtra->thenLit, synExtra->elseLit);
    if (resAnsLit) {
      LiteralStack lits(cl->length()-1);
      for (unsigned i = 0; i < cl->length(); ++i) {
        // Apply the substitution on all literals except the answer literals
        if ((i != idx[0]) && (i != idx[1])) {
          Literal* lit = subst.apply((*cl)[i], 0);
          lits.push(subst.apply((*cl)[i], 0));
        }
      }
      // Add the unified answer literal
      lits.push(resAnsLit);
      ASS(lits.top()->computableOrVar());
      Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_UNIFICATION, cl));
      replacement = Clause::fromStack(lits, inf);
    } else {
      // Cannot join the answer literals, fail
      return nullptr;
    }
  }

  return replacement;
}

}
