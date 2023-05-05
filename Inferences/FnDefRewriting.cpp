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
 * @file FnDefRewriting.cpp
 * Implements class FnDefRewriting.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/FunctionDefinitionHandler.hpp"

#include "FnDefRewriting.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

struct FnDefRewriting::GeneralizationsFn {
  GeneralizationsFn(FunctionDefinitionHandler *index) : _index(index) {}
  VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>> operator()(pair<Literal *, TermList> arg)
  {
    CALL("FnDefRewriting::GeneralizationsFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second)));
  }

private:
  FunctionDefinitionHandler *_index;
};

struct FnDefRewriting::RewriteableSubtermsFn {
  VirtualIterator<pair<Literal *, TermList>> operator()(Literal *lit)
  {
    CALL("FnDefRewriting::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi(pushPairIntoRightIterator(lit,
                                         getUniquePersistentIteratorFromPtr(&nvi)));
  }
};

struct FnDefRewriting::ForwardResultFn {
  ForwardResultFn(Clause *cl) : _cl(cl) {}

  Clause* operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("FnDefRewriting::ForwardResultFn()");

    TermQueryResult &qr = arg.second;
    bool temp;
    return FnDefRewriting::perform(_cl, arg.first.first, arg.first.second, qr.clause,
                                   qr.literal, qr.term, qr.substitution, false, temp,
                                   Inference(GeneratingInference2(InferenceRule::FNDEF_REWRITING, _cl, qr.clause)));
  }
private:
  Clause *_cl;
};

ClauseIterator FnDefRewriting::generateClauses(Clause *premise)
{
  CALL("FnDefRewriting::generateClauses");

  auto itf1 = premise->iterLits();

  // Get an iterator of pairs of selected literals and rewritable subterms
  // of those literals. Here all subterms of a literal are rewritable.
  auto itf2 = getMapAndFlattenIterator(itf1, RewriteableSubtermsFn());

  // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
  // returns a pair with the original pair and the generalization result (includes substitution)
  auto itf3 = getMapAndFlattenIterator(itf2, GeneralizationsFn(GeneratingInferenceEngine::_salg->getFunctionDefinitionHandler()));

  //Perform forward rewriting
  auto it = pvi(getMappingIterator(itf3, ForwardResultFn(premise)));
  // Remove null elements
  return pvi(getFilteredIterator(it, NonzeroFn()));
}

bool FnDefRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("FnDefRewriting::perform/1");
  auto salg = ForwardSimplificationEngine::_salg;

  Ordering& ordering = salg->getOrdering();

  static DHSet<TermList> attempted;
  attempted.reset();

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    NonVariableIterator it(lit);
    while (it.hasNext()) {
      TermList trm = it.next();
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }

      bool toplevelCheck = salg->getOptions().demodulationRedundancyCheck()!=Options::DemodulationRedunancyCheck::OFF &&
        lit->isEquality() && (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

      auto git = salg->getFunctionDefinitionHandler()->getGeneralizations(trm);
      while (git.hasNext()) {
        TermQueryResult qr = git.next();
        if (qr.clause->length() != 1) {
          continue;
        }
        auto rhs = EqHelper::getOtherEqualitySide(qr.literal, qr.term);
        if (Ordering::isGorGEorE(ordering.compare(rhs,qr.term))) {
          continue;
        }
        bool isEqTautology = false;
        auto res = FnDefRewriting::perform(cl, lit, trm, qr.clause, qr.literal, qr.term, qr.substitution, toplevelCheck,
          isEqTautology, Inference(SimplifyingInference2(InferenceRule::FNDEF_DEMODULATION, cl, qr.clause)), salg);
        if (!res && !isEqTautology) {
          continue;
        }
        if (!isEqTautology) {
          replacement = res;
        }
        premises = pvi(getSingletonIterator(qr.clause));
        return true;
      }
    }
  }

  return false;
}

Clause *FnDefRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool toplevelCheck, bool& isEqTautology,
    const Inference& inf, SaturationAlgorithm* salg)
{
  CALL("FnDefRewriting::perform/2");

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  TermList tgtTermS;
  if (!subst->isIdentityOnQueryWhenResultBound()) {
    //When we apply substitution to the rhs, we get a term, that is
    //a variant of the term we'd like to get, as new variables are
    //produced in the substitution application.
    TermList lhsSBadVars = subst->applyToResult(eqLHS);
    TermList rhsSBadVars = subst->applyToResult(tgtTerm);
    Renaming rNorm, qNorm, qDenorm;
    rNorm.normalizeVariables(lhsSBadVars);
    qNorm.normalizeVariables(tgtTerm);
    qDenorm.makeInverse(qNorm);
    ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
    tgtTermS = qDenorm.apply(rNorm.apply(rhsSBadVars));
  }
  else {
    tgtTermS = subst->applyToBoundResult(tgtTerm);
  }

  // update this to latest encompassment-considering version
  if (toplevelCheck) {
    Ordering& ordering = salg->getOrdering();
    TermList other=EqHelper::getOtherEqualitySide(rwLit, rwTerm);
    Ordering::Result tord = ordering.compare(tgtTermS, other);
    if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {
      Literal* eqLitS = subst->applyToBoundResult(eqLit);
      bool isMax=true;
      for (unsigned i = 0; i < rwClause->length(); i++) {
        if (rwLit == (*rwClause)[i]) {
          continue;
        }
        if (ordering.compare(eqLitS, (*rwClause)[i]) == Ordering::LESS) {
          isMax=false;
          break;
        }
      }
      if (isMax) {
        return 0;
      }
    }
  }

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    isEqTautology = true;
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Clause *res = new (newLength) Clause(newLength, inf);

  static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (doSimS) {
        curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      }

      if (EqHelper::isEqTautology(curr)) {
        isEqTautology = true;
        res->destroy();
        return 0;
      }

      (*res)[next++] = curr;
    }
  }

  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter;
        if (!subst->isIdentityOnQueryWhenResultBound()) {
          // same as above for RHS
          TermList lhsSBadVars = subst->applyToResult(eqLHS);
          Literal *currSBadVars = subst->applyToResult(curr);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(curr);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = subst->applyToBoundResult(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          isEqTautology = true;
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  return res;
}
