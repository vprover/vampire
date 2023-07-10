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
 * @file RewritingByRule.cpp
 * Implements class RewritingByRule.
 */

#include "RewritingByRule.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/RewritingData.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

using namespace Kernel;
using namespace Inferences;

ClauseIterator SuperpositionByRule::generateClauses(Clause* c)
{
  CALL("SuperpositionByRule::generateClauses");

  auto& ord = _salg->getOrdering();
  auto rwData = c->rewritingData();
  auto stats = env.statistics;

  return pvi(iterTraits(c->getSelectedLiteralIterator())
    .flatMap([&ord](Literal* lit) {
      VirtualIterator<Term*> it = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, ord) :
                                                                  EqHelper::getSubtermIterator(lit, ord);
      return pvi(pushPairIntoRightIterator(lit, it));
    })
    .flatMap([rwData](pair<Literal*, Term*> kv) {
      return pvi(pushPairIntoRightIterator(kv, rwData->items()));
    })
    .map([c,&ord,stats](pair<pair<Literal*, Term*>,pair<Term*,TermList>> arg) -> Clause* {
      TermList rwTerm(arg.first.second);
      TermList eqLHS(arg.second.first);
      auto tgtTerm = arg.second.second;

      RobSubstitution subst;
      if (tgtTerm.isEmpty() || !subst.unify(eqLHS,0,rwTerm,0)) {
        return nullptr;
      }
      
      TermList eqLHSS = subst.apply(eqLHS, 0);
      TermList tgtTermS = subst.apply(tgtTerm, 0);
      Literal* rwLitS = subst.apply(arg.first.first, 0);

      //check that we're not rewriting smaller subterm with larger
      if (Ordering::isGorGEorE(ord.compare(tgtTermS,eqLHSS))) {
        return nullptr;
      }

      if (rwLitS->isEquality()) {
        // check that we're not rewriting only the smaller side of an equality
        TermList arg0 = rwLitS->termArg(0);
        TermList arg1 = rwLitS->termArg(1);

        if(!arg0.containsSubterm(eqLHSS)) {
          if(Ordering::isGorGEorE(ord.getEqualityArgumentOrder(rwLitS))) {
            return nullptr;
          }
        } else if(!arg1.containsSubterm(eqLHSS)) {
          if(Ordering::isGorGEorE(Ordering::reverse(ord.getEqualityArgumentOrder(rwLitS)))) {
            return nullptr;
          }
        }
        if (arg0 == eqLHSS || arg1 == eqLHSS) {
          auto other = arg0 == eqLHSS ? arg1 : arg0;
          Ordering::Result tord=ord.compare(tgtTermS, other);
          if (tord !=Ordering::LESS && tord!=Ordering::LESS_EQ) {
            return nullptr;
          }
        }
      }

      Clause* res = new(c->length()) Clause(c->length(), GeneratingInference1(InferenceRule::SUPERPOSITION_BY_RULE, c));
      for (unsigned i = 0;i < c->length(); i++) {
        Literal* currAfter = EqHelper::replace(subst.apply((*c)[i], 0),eqLHSS,tgtTermS);
        if(EqHelper::isEqTautology(currAfter)) {
          res->destroy();
          return nullptr;
        }
        (*res)[i] = currAfter;
      }

      {
        TIME_TRACE("diamond-breaking-r");
        auto rwData = res->rewritingData();
        c->rewritingData()->copy(rwData, [&subst](TermList t) { return subst.apply(t,0); });
      }
      // auto rwstit = RewriteableSubtermsFn(ordering)(rwLit);
      // while (rwstit.hasNext()) {
      //   auto st = subst->apply(rwstit.next().second, eqIsResult);
      //   if (ordering.compare(rwTermS, st)==Ordering::Result::GREATER) {
      //     // cout << "adding blocked " << st << " for " << rwTermS << endl;
      //     res->addBlockedTerm(st);
      //   }
      // }
      // res->addRewriteRule(eqLHSS,tgtTermS);

      stats->superpositionByRule++;

      // cout << "superposition " << rwTerm << " in " << *c << endl
      //      << "by rule       " << eqLHS << " -> " << tgtTerm << endl
      //      << "result        " << *res << endl << endl;
      return res;
    })
    .filter(NonzeroFn())
    .timeTraced("superposition by rule"));
}

Clause* DemodulationByRule::simplify(Clause* c)
{
  CALL("DemodulationByRule::simplify");
  TIME_TRACE("demodulation by rule");

  auto cLen = c->length();
  auto& ord = _salg->getOrdering();
  for (unsigned i = 0; i < cLen; i++) {
    auto lit = (*c)[i];
    auto it = c->rewritingData()->items();
    while (it.hasNext()) {
      auto kv = it.next();
      TermList lhs(kv.first);
      if (kv.second.isEmpty() || !lit->containsSubterm(lhs)) {
        continue;
      }
      if (ord.compare(lhs,kv.second)!=Ordering::GREATER) {
        continue;
      }
      if (lit->isEquality() && (lit->termArg(0) == lhs || lit->termArg(1) == lhs)) {
        // TODO: perform demodulation redundancy check
        auto other = lit->termArg(0) == lhs ? lit->termArg(1) : lit->termArg(0);
        Ordering::Result tord=ord.compare(kv.second, other);
        if (tord !=Ordering::LESS && tord!=Ordering::LESS_EQ) {
          // bool isMax = true;
          // for (unsigned j = 0; j < cLen; j++) {
          //   if (lit == (*c)[j]) {
          //     continue;
          //   }
          //   if (ord.compare(lit, (*c)[j]) == Ordering::LESS) {
          //     isMax=false;
          //     break;
          //   }
          // }
          // if(isMax) {
            // cout << "rule " << kv.first << "->" << kv.second << ", cl: " << *c << endl;
            continue;
          // }
        }
      }

      Clause* res = new(cLen) Clause(cLen,
        SimplifyingInference1(InferenceRule::DEMODULATION_BY_RULE, c));
      for(unsigned j=0;j<cLen;j++) {
        (*res)[j] = EqHelper::replace((*c)[j],lhs,kv.second);
      }
      c->rewritingData()->copy(res->rewritingData(),[](TermList t) { return t; });
      env.statistics->demodulationByRule++;
      return res;
    }
  }
  return c;
}
