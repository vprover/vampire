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
 * @file FunctionDefinitionRewriting.cpp
 * Implements class FunctionDefinitionRewriting.
 */

#include "Indexing/Index.hpp"
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

#include "FunctionDefinitionRewriting.hpp"

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

Kernel::ClauseIterator FunctionDefinitionRewriting::generateClauses(Clause *premise)
{
  return pvi(premise->iterLits()
    .flatMap([](Literal *lit) {
      NonVariableNonTypeIterator nvi(lit);
      return pvi(pushPairIntoRightIterator(lit, getUniquePersistentIteratorFromPtr(&nvi)));
    })
    .flatMap([this](std::pair<Literal*, Term*> arg){
      return pvi(pushPairIntoRightIterator(arg,
        GeneratingInferenceEngine::_salg->getFunctionDefinitionHandler().getGeneralizations(arg.second)));
    })
    .map([premise](auto arg) {
      auto &qr = arg.second;
      bool temp;
      return (Clause*)FunctionDefinitionRewriting::perform(premise, arg.first.first, TermList(arg.first.second), qr.data->clause,
        qr.data->literal, qr.data->term, qr.unifier, false, temp,
        Inference(GeneratingInference2(InferenceRule::FUNCTION_DEFINITION_REWRITING, premise, qr.data->clause)));
    })
    .filter(NonzeroFn()));
}

bool FunctionDefinitionRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  auto salg = ForwardSimplificationEngine::_salg;

  Ordering& ordering = salg->getOrdering();

  static DHSet<Term*> attempted;
  attempted.reset();

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      TypedTermList trm = it.next();
      if (!attempted.insert(trm.term())) {
        it.right();
        continue;
      }

      bool toplevelCheck = salg->getOptions().demodulationRedundancyCheck()!=Options::DemodulationRedunancyCheck::OFF &&
        lit->isEquality() && (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

      auto git = salg->getFunctionDefinitionHandler().getGeneralizations(trm);
      while (git.hasNext()) {
        auto qr = git.next();
        if (qr.data->clause->length() != 1) {
          continue;
        }
        auto rhs = EqHelper::getOtherEqualitySide(qr.data->literal, qr.data->term);
        // TODO shouldn't allow demodulation with incomparables in the non-ground case
        if (Ordering::isGorGEorE(ordering.compare(rhs,qr.data->term))) {
          continue;
        }
        bool isEqTautology = false;
        auto res = FunctionDefinitionRewriting::perform(cl, lit, trm, qr.data->clause, qr.data->literal, qr.data->term, qr.unifier, toplevelCheck,
          isEqTautology, Inference(SimplifyingInference2(InferenceRule::FUNCTION_DEFINITION_DEMODULATION, cl, qr.data->clause)), salg);
        if (!res && !isEqTautology) {
          continue;
        }
        if (!isEqTautology) {
          replacement = res;
        }
        premises = pvi(getSingletonIterator(qr.data->clause));
        return true;
      }
    }
  }

  return false;
}

Clause *FunctionDefinitionRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool toplevelCheck, bool& isEqTautology,
    const Inference& inf, SaturationAlgorithm* salg)
{
  if (SortHelper::getResultSort(rwTerm.term()) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  // This should be the case for code trees
  ASS(subst->isIdentityOnQueryWhenResultBound());
  TermList tgtTermS = subst->applyToBoundResult(tgtTerm);

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

  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr == rwLit) {
      continue;
    }
    curr = EqHelper::replace(curr, rwTerm, tgtTermS);

    if (EqHelper::isEqTautology(curr)) {
      isEqTautology = true;
      res->destroy();
      return 0;
    }

    (*res)[next++] = curr;
  }

  for (unsigned i = 0; i < eqLength; i++) {
    Literal* curr = (*eqClause)[i];
    if (curr == eqLit) {
      continue;
    }
    Literal* currAfter = subst->applyToBoundResult(curr);

    if (EqHelper::isEqTautology(currAfter)) {
      isEqTautology = true;
      res->destroy();
      return 0;
    }

    (*res)[next++] = currAfter;
  }

  return res;
}
