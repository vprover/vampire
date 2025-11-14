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
#include "Kernel/Term.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/FunctionDefinitionHandler.hpp"

#include "FunctionDefinitionRewriting.hpp"

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

namespace {
struct Applicator : SubstApplicator {
  Applicator(ResultSubstitution* subst) : subst(subst) {}
  TermList operator()(unsigned v) const override {
    return subst->applyToBoundResult(v);
  }
  ResultSubstitution* subst;
};
}

Clause* performRewriting(
    Clause *rwClause, Literal *rwLit, TermList rwTerm, Clause *eqClause,
    Literal *eqLit, TermList eqLHS, ResultSubstitutionSP subst,
    DemodulationHelper* helper, bool& isEqTautology, Inference&& inf)
{
  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  // This should be the case for code trees
  ASS(subst->isIdentityOnQueryWhenResultBound());
  TermList tgtTermS = subst->applyToBoundResult(tgtTerm);

  Applicator appl(subst.ptr());

  if (helper && !helper->isPremiseRedundant(rwClause,rwLit,rwTerm,tgtTermS,eqLHS,&appl)) {
    return 0;
  }

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    isEqTautology = true;
    return 0;
  }

  RStack<Literal*> resLits;

  resLits->push(tgtLitS);

  for (Literal *curr : rwClause->iterLits()) {
    if (curr == rwLit) {
      continue;
    }
    curr = EqHelper::replace(curr, rwTerm, tgtTermS);

    if (EqHelper::isEqTautology(curr)) {
      isEqTautology = true;
      return nullptr;
    }

    resLits->push(curr);
  }

  for (Literal* curr : eqClause->iterLits()) {
    if (curr == eqLit) {
      continue;
    }
    Literal* currAfter = subst->applyToBoundResult(curr);

    if (EqHelper::isEqTautology(currAfter)) {
      isEqTautology = true;
      return nullptr;
    }

    resLits->push(currAfter);
  }

  return Clause::fromStack(*resLits, inf);
}

void FunctionDefinitionRewriting::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _helper = DemodulationHelper(salg->getOptions(), &salg->getOrdering());
}

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
      return (Clause*)performRewriting(premise, arg.first.first, TermList(arg.first.second), qr.data->clause,
        qr.data->literal, qr.data->term, qr.unifier, nullptr, temp,
        Inference(GeneratingInference2(InferenceRule::FUNCTION_DEFINITION_REWRITING, premise, qr.data->clause)));
    })
    .filter(NonzeroFn()));
}

void FunctionDefinitionDemodulation::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _helper = DemodulationHelper(salg->getOptions(), &salg->getOrdering());
}

bool FunctionDefinitionDemodulation::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

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

      bool redundancyCheck = _helper.redundancyCheckNeededForPremise(cl, lit, trm);

      auto git = _salg->getFunctionDefinitionHandler().getGeneralizations(trm);
      while (git.hasNext()) {
        auto qr = git.next();
        if (qr.data->clause->length() != 1) {
          continue;
        }
        auto rhs = EqHelper::getOtherEqualitySide(qr.data->literal, qr.data->term);
        // TODO shouldn't allow demodulation with incomparables in the non-ground case
        if (Ordering::isGreaterOrEqual(ordering.compare(rhs,qr.data->term))) {
          continue;
        }
        bool isEqTautology = false;
        auto res = performRewriting(
          cl, lit, trm, qr.data->clause, qr.data->literal, qr.data->term, qr.unifier, redundancyCheck ? &_helper : nullptr,
          isEqTautology, Inference(SimplifyingInference2(InferenceRule::FUNCTION_DEFINITION_DEMODULATION, cl, qr.data->clause)));
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
