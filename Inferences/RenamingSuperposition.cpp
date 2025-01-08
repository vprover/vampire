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
 * @file RenamingSuperposition.cpp
 * Implements class RenamingSuperposition.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/ConditionalRedundancyHandler.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "DemodulationHelper.hpp"

#include "RenamingSuperposition.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace std;

namespace {

struct Applicator : SubstApplicator {
  Applicator(ResultSubstitution* subst) : subst(subst) {}
  TermList operator()(unsigned v) const override {
    return subst->applyToBoundResult(v);
  }
  ResultSubstitution* subst;
};

} // end namespace

void RenamingSuperposition::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  if (salg->getOptions().demodulationRedundancyCheck()!=Options::DemodulationRedundancyCheck::ENCOMPASS) {
    INVALID_OPERATION("RenamingSuperposition only works with drc=encompass");
  }
  // TODO use a generating index
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void RenamingSuperposition::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  GeneratingInferenceEngine::detach();
}

ClauseIterator RenamingSuperposition::generateClauses(Clause* cl)
{
  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;
  attempted.reset();
  auto res = ClauseIterator::getEmpty();

  if (cl->length()>1) {
    return res;
  }

  auto clit = (*cl)[0];
  if (!clit->isEquality() || clit->isNegative()) {
    return res;
  }

  auto tod = ordering.createComparator(false).release();
  tod->insert({ { clit->termArg(0), clit->termArg(1), Ordering::EQUAL } }, (void*)0x1);

  NonVariableNonTypeIterator it(clit);
  while (it.hasNext()) {
    TermList trm(it.next());
    if (!attempted.insert(trm)) {
      it.right();
      continue;
    }
    bool redundancyCheck = false;
    if (trm == clit->termArg(0) && ordering.getEqualityArgumentOrder(clit) != Ordering::LESS) {
      redundancyCheck = true;
    }
    if (trm == clit->termArg(1) && ordering.getEqualityArgumentOrder(clit) != Ordering::GREATER) {
      redundancyCheck = true;
    }

    auto git = _index->getGeneralizations(trm.term(), /* retrieveSubstitutions */ true);
    while (git.hasNext()) {
      auto qr=git.next();
      ASS_EQ(qr.data->clause->length(),1);

      auto lhs = qr.data->term;
      if (lhs.isVar()) {
        // we are not interested in these for now
        continue;
      }

      auto subs = qr.unifier;
      ASS(subs->isIdentityOnQueryWhenResultBound());
      Applicator appl(subs.ptr());
      AppliedTerm rhsApplied(qr.data->rhs, &appl, true);

      auto comp = ordering.compare(rhsApplied,trm);
      if (Ordering::isGreaterOrEqual(comp)) {
        continue;
      }

      Ordering::Result redComp = Ordering::LESS;
      if (redundancyCheck && DemodulationHelper::isRenamingOn(&appl,lhs)) {
        redComp = ordering.compare(rhsApplied, EqHelper::getOtherEqualitySide(clit, trm));
        if (Ordering::isGreaterOrEqual(redComp)) {
          continue;
        }
      }

      // one of them has to be incomparable otherwise we would have demodulated
      ASS(comp == Ordering::INCOMPARABLE || redComp == Ordering::INCOMPARABLE);

      TermList rhsS = rhsApplied.apply();
      Stack<TermOrderingConstraint> constraints;
      if (comp == Ordering::INCOMPARABLE) {
        constraints.push({ trm, rhsS, Ordering::GREATER });
      }
      if (redComp == Ordering::INCOMPARABLE) {
        constraints.push({ EqHelper::getOtherEqualitySide(clit, trm), rhsS, Ordering::GREATER });
      }

      Shell::ConditionalRedundancySubsumption subsumption(*tod, ordering, constraints, true);
      if (subsumption.check()) {
        env.statistics->generalizedInductionApplicationInProof++;
        continue;
      }
      tod->insert(constraints, (void*)0x1);

      RStack<Literal*> resLits;
      resLits->push(EqHelper::replace(clit,trm,rhsS));

      for(unsigned i=0;i<cl->length();i++) {
        Literal* curr=(*cl)[i];
        if(curr!=clit) {
          resLits->push(curr);
        }
      }

      env.statistics->generalizedInductionApplication++;

      res = pvi(concatIters(res,getSingletonIterator(
        Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::INDUCTION_HYPERRESOLUTION, cl, qr.data->clause)))));
    }
  }

  Shell::ConditionalRedundancySubsumption subs(*tod, ordering, Stack<TermOrderingConstraint>(), /*ground=*/true);
  if (subs.check()) {
    cl->markRedundant();
    env.statistics->groundRedundantClauses++;
  }
  cl->setTod(tod);

  return res;
}

}