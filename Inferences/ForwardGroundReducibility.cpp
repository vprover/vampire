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
 * @file ForwardGroundReducibility.cpp
 * Implements class ForwardGroundReducibility.
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

#include "ForwardGroundReducibility.hpp"

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

void ForwardGroundReducibility::attach(SaturationAlgorithm* salg)
{
  ForwardGroundSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void ForwardGroundReducibility::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardGroundSimplificationEngine::detach();
}

bool ForwardGroundReducibility::perform(Clause* cl, ClauseIterator& replacements, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;
  DHSet<Clause*> premiseSet;
  attempted.reset();
  auto res = ClauseIterator::getEmpty();
  auto tod = ordering.createComparator(/*onlyVars=*/true, /*ground=*/true).release();

  bool clRedCheck = cl->length()==1 && (*cl)[0]->isPositive() && (*cl)[0]->isEquality();

  for (unsigned i = 0; i < cl->length(); i++) {
    auto clit = (*cl)[i];
    if (clit->isEquality() && clit->isPositive()) {
      tod->insert({ { clit->termArg(0), clit->termArg(1), Ordering::EQUAL } }, this);
    }

    NonVariableNonTypeIterator it(clit);
    while (it.hasNext()) {
      TermList trm(it.next());
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }
      bool redundancyCheck = false;
      if (clRedCheck && trm == clit->termArg(0) && ordering.getEqualityArgumentOrder(clit) != Ordering::LESS) {
        redundancyCheck = true;
      }
      if (clRedCheck && trm == clit->termArg(1) && ordering.getEqualityArgumentOrder(clit) != Ordering::GREATER) {
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

        auto tod2 = ordering.createComparator();
        tod2->insert(constraints, this);
        Shell::ConditionalRedundancySubsumption subsumption(*tod, *tod2, true);
        if (subsumption.check()) {
          continue;
        }
        tod->insert(constraints, this);

        RStack<Literal*> resLits;
        resLits->push(EqHelper::replace(clit,trm,rhsS));

        for(unsigned i=0;i<cl->length();i++) {
          Literal* curr=(*cl)[i];
          if(curr!=clit) {
            resLits->push(curr);
          }
        }

        auto resCl = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_GROUND_REDUCIBILITY, cl, qr.data->clause));
        premiseSet.insert(qr.data->clause);
        OrderingComparator* infTod = ordering.createComparator(false, true).release();
        OrderingConstraints ordCons;
        if (comp == Ordering::INCOMPARABLE) {
          ordCons.push({ trm, rhsApplied.apply(), Ordering::GREATER });
        }
        infTod->insert(ordCons, resCl);
        resCl->setInfTod(infTod);
        res = pvi(concatIters(res,getSingletonIterator(resCl)));
      }
    }
  }

  auto todOther = ordering.createComparator();
  todOther->insert(OrderingConstraints(), this);
  Shell::ConditionalRedundancySubsumption subs(*tod, *todOther, /*ground=*/true);
  if (subs.check()) {
    cl->markRedundant();
    env.statistics->forwardGroundReducibility++;
    replacements = res;
    premises = pvi(getPersistentIterator(premiseSet.iterator()));
    return true;
  }
  // cl->setTod(tod);
  return false;
}

}