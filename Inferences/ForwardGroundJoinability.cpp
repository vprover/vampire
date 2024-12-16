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
 * @file ForwardGroundJoinability.cpp
 * Implements class ForwardGroundJoinability.
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

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "DemodulationHelper.hpp"

#include "ForwardGroundJoinability.hpp"

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

void ForwardGroundJoinability::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void ForwardGroundJoinability::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

using Position = Stack<unsigned>;

bool toTheLeftStrict(const Position& p1, const Position& p2, bool& prefix)
{
  prefix = false;
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return false;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  prefix = true;
  return false;
}

bool isUnderVariablePosition(const Position& p, TermList lhs)
{
  if (lhs.isVar()) {
    return true;
  }
  auto curr = lhs.term();
  for (unsigned i = 0; i < p.size(); i++) {
    ASS_L(p[i],curr->arity());
    auto next = *curr->nthArgument(i);
    if (next.isVar()) {
      return true;
    }
    curr = next.term();
  }
  return false;
}

string posToString(const Position& pos)
{
  string res;
  for (const auto& i : pos) {
    res += "." + Int::toString(i);
  }
  return res;
}

bool ForwardGroundJoinability::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;

  if (cl->length()>1) {
    return false;
  }

  auto clit = (*cl)[0];
  if (!clit->isEquality() || clit->isNegative()) {
    return false;
  }
  DHSet<Clause*> premiseSet;

  OrderingComparator::RedundancyCheck checker(ordering, clit);
  Literal* lit = clit;
  auto tpo = TermPartialOrdering::getEmpty(ordering);
  unsigned cnt = 0;

  while (lit) {
    if (cnt++ > 500) {
      return false;
    }
    attempted.reset();

    auto kv = checker.next({ { lit->termArg(0), lit->termArg(1), Ordering::EQUAL } }, nullptr);
    lit = static_cast<Literal*>(kv.first);
    tpo = kv.second;
    if (!lit) {
      break;
    }

    PolishSubtermIterator it(lit);
    while (it.hasNext()) {
      TermList t = it.next();
      if (t.isVar()) {
        continue;
      }
      TypedTermList trm = t.term();
      if (!attempted.insert(trm)) {
        continue;
      }

      ASS(lit->isPositive());
      bool redundancyCheck = (trm == lit->termArg(0) || trm == lit->termArg(1));

      auto git = _index->getGeneralizations(trm.term(), /* retrieveSubstitutions */ true);
      while(git.hasNext()) {
        auto qr=git.next();
        ASS_EQ(qr.data->clause->length(),1);

        if(!ColorHelper::compatible(cl->color(), qr.data->clause->color())) {
          continue;
        }

        auto lhs = qr.data->term;
        if (lhs.isVar()) {
          // we are not interested in these for now
          continue;
        }

        TermList rhs = qr.data->rhs;

        auto subs = qr.unifier;
        ASS(subs->isIdentityOnQueryWhenResultBound());

        Applicator appl(subs.ptr());

        OrderingConstraints cons;

        TermList rhsS;

        Result comp;
        if (flag) {
          ASS(tpo);
          comp = ordering.compare(AppliedTerm(lhs, &appl, true), AppliedTerm(rhs, &appl, true), tpo);
        } else {
          comp = ordering.compare(AppliedTerm(lhs, &appl, true), AppliedTerm(rhs, &appl, true));
        }
        if (comp == Ordering::LESS || comp == Ordering::EQUAL) {
          continue;
        } else if (comp == Ordering::INCOMPARABLE) {
          rhsS = subs->applyToBoundResult(rhs);
          cons.push({ trm, rhsS, Ordering::GREATER });
        }

        // encompassing demodulation is fine when rewriting the smaller guy
        if (redundancyCheck) {
          // this will only run at most once;
          // could have been factored out of the getGeneralizations loop,
          // but then it would run exactly once there
          Ordering::Result litOrder = ordering.getEqualityArgumentOrder(lit);
          if ((trm==lit->termArg(0) && litOrder == Ordering::LESS) ||
              (trm==lit->termArg(1) && litOrder == Ordering::GREATER)) {
            redundancyCheck = false;
          }
        }

        if (redundancyCheck && DemodulationHelper::isRenamingOn(&appl,lhs)) {
          TermList other = trm == lit->termArg(0) ? lit->termArg(1) : lit->termArg(0);
          auto redComp = ordering.compare(AppliedTerm(rhs, &appl, true), AppliedTerm(other));
          if (redComp == Ordering::LESS || redComp == Ordering::EQUAL) {
            continue;
          } else if (redComp == Ordering::INCOMPARABLE) {
            if (rhsS.isEmpty()) {
              rhsS = subs->applyToBoundResult(rhs);
            }
            cons.push({ other, rhsS, Ordering::GREATER });
          }
        }

        if (rhsS.isEmpty()) {
          rhsS = subs->applyToBoundResult(rhs);
        }

        std::pair<void*,const TermPartialOrdering*> next;
        Literal* resLit = EqHelper::replace(lit,trm,rhsS);
        if (EqHelper::isEqTautology(resLit)) {
          next = checker.next(cons, nullptr);
        } else {
          next = checker.next(cons, resLit);
        }
        env.statistics->structInduction++;
        tpo = next.second;
        if (next.first != lit) {
          env.statistics->structInductionInProof++;
          lit = (Literal*)next.first;
          premiseSet.insert(qr.data->clause);
          goto LOOP_END;
        }
      }
    }
    return false;
LOOP_END:
    continue;
  }
  premises = pvi(getPersistentIterator(premiseSet.iterator()));

  env.statistics->groundRedundantClauses++;
  return true;
}

}