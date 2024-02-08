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

// ClauseIterator SuperpositionByRule::generateClauses(Clause* c)
// {
//   CALL("SuperpositionByRule::generateClauses");

//   auto& ord = _salg->getOrdering();
//   auto rwData = c->rewritingData();
//   auto stats = env.statistics;

//   return pvi(iterTraits(c->getSelectedLiteralIterator())
//     .flatMap([&ord](Literal* lit) {
//       VirtualIterator<Term*> it = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, ord) :
//                                                                   EqHelper::getSubtermIterator(lit, ord);
//       return pvi(pushPairIntoRightIterator(lit, it));
//     })
//     .flatMap([rwData](pair<Literal*, Term*> kv) {
//       return pvi(pushPairIntoRightIterator(kv, rwData->items()));
//     })
//     .map([c,&ord,stats](pair<pair<Literal*, Term*>,pair<Term*,pair<TermList,TermQueryResult>>> arg) -> Clause* {
//       TermList rwTerm(arg.first.second);
//       TermList eqLHS(arg.second.first);
//       auto tgtTerm = arg.second.second.first;
//       auto qr = arg.second.second.second;

//       RobSubstitution subst;
//       if (tgtTerm.isEmpty() || !subst.unify(eqLHS,0,rwTerm,0)) {
//         return nullptr;
//       }
      
//       TermList eqLHSS = subst.apply(eqLHS, 0);
//       TermList tgtTermS = subst.apply(tgtTerm, 0);
//       Literal* rwLitS = subst.apply(arg.first.first, 0);

//       //check that we're not rewriting smaller subterm with larger
//       if (Ordering::isGorGEorE(ord.compare(tgtTermS,eqLHSS))) {
//         return nullptr;
//       }

//       if (rwLitS->isEquality()) {
//         // check that we're not rewriting only the smaller side of an equality
//         TermList arg0 = rwLitS->termArg(0);
//         TermList arg1 = rwLitS->termArg(1);

//         if(!arg0.containsSubterm(eqLHSS)) {
//           if(Ordering::isGorGEorE(ord.getEqualityArgumentOrder(rwLitS))) {
//             return nullptr;
//           }
//         } else if(!arg1.containsSubterm(eqLHSS)) {
//           if(Ordering::isGorGEorE(Ordering::reverse(ord.getEqualityArgumentOrder(rwLitS)))) {
//             return nullptr;
//           }
//         }
//         if (arg0 == eqLHSS || arg1 == eqLHSS) {
//           auto other = arg0 == eqLHSS ? arg1 : arg0;
//           Ordering::Result tord=ord.compare(tgtTermS, other);
//           if (tord !=Ordering::LESS && tord!=Ordering::LESS_EQ) {
//             return nullptr;
//           }
//         }
//       }

//       ALWAYS(subst.unify(rwTerm,0,qr.term,1));

//       Literal* tgtLitS = EqHelper::replace(rwLitS,eqLHSS,tgtTermS);
//       if (EqHelper::isEqTautology(tgtLitS)) {
//         return nullptr;
//       }

//       unsigned newLen = c->length() + qr.clause->length() - 1;
//       Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::SUPERPOSITION_BY_RULE, c));
//       (*res)[0] = EqHelper::replace(rwLitS,eqLHSS,tgtTermS);
//       unsigned next = 1;
//       for (unsigned i = 0; i < c->length(); i++) {
//         auto curr = (*c)[i];
//         if (curr == arg.first.first) {
//           continue;
//         }
//         Literal* currAfter = subst.apply(curr, 0);
//         (*res)[next++] = currAfter;
//       }

//       for (unsigned i = 0; i < qr.clause->length(); i++) {
//         auto curr = (*qr.clause)[i];
//         if (curr == qr.literal) {
//           continue;
//         }
//         Literal* currAfter = subst.apply(curr, 1);
//         (*res)[next++] = currAfter;
//       }

//       {
//         TIME_TRACE("diamond-breaking-r");
//         auto rwData = res->rewritingData();
//         if (!c->rewritingData()->copy(rwData, [&subst](TermList t) { return subst.apply(t,0); })) {
//           env.statistics->skipped++;
//           TIME_TRACE("rewriting by rule skipped");
//           return nullptr;
//         }
//       }
//       // auto rwstit = RewriteableSubtermsFn(ordering)(rwLit);
//       // while (rwstit.hasNext()) {
//       //   auto st = subst->apply(rwstit.next().second, eqIsResult);
//       //   if (ordering.compare(rwTermS, st)==Ordering::Result::GREATER) {
//       //     // cout << "adding blocked " << st << " for " << rwTermS << endl;
//       //     res->addBlockedTerm(st);
//       //   }
//       // }
//       // res->addRewriteRule(eqLHSS,tgtTermS);

//       stats->superpositionByRule++;

//       // cout << "superposition " << rwTerm << " in " << *c << endl
//       //      << "by rule       " << eqLHS << " -> " << tgtTerm << endl
//       //      << "clause        " << *qr.clause << endl
//       //      << "result        " << *res << endl << endl;
//       return res;
//     })
//     .filter(NonzeroFn())
//     .timeTraced("superposition by rule"));
// }

Clause* DemodulationByRule::simplify(Clause* c)
{
  TIME_TRACE("demodulation by rule");

  auto cLen = c->length();
  auto& ord = _salg->getOrdering();
  auto rwData = c->rewritingData();
  if (!rwData) {
    return c;
  }
  DHSet<Term*> attempted;
  for (unsigned i = 0; i < cLen; i++) {
    auto lit = (*c)[i];
    NonVariableNonTypeIterator nvi(lit);
    while (nvi.hasNext()) {
      auto st = nvi.next();
      if (!attempted.insert(st)) {
        nvi.right();
        continue;
      }
      TermList rhs;
      if (!rwData->contains(st,rhs) || rhs.isEmpty()) {
        continue;
      }
      TermList lhs(st);
      if (!ord.isGreater(lhs,rhs)) {
        continue;
      }
      if (lit->isEquality() && (lit->termArg(0) == lhs || lit->termArg(1) == lhs)) {
        // simply skip this for now, it is usually unsound
        continue;
      }

      Clause* res = new(cLen) Clause(cLen,
        SimplifyingInference1(InferenceRule::DEMODULATION_BY_RULE, c));
      (*res)[0]=EqHelper::replace(lit,lhs,rhs);
      unsigned next=1;
      for(unsigned i=0;i<cLen;i++) {
        Literal* curr=(*c)[i];
        if(curr!=lit) {
          (*res)[next++] = curr;
        }
      }
      ASS_EQ(next,cLen);
      if (c->rewritingData()) {
        res->setRewritingData(new RewritingData(_salg->getOrdering()));
        res->rewritingData()->copyRewriteRules(c->rewritingData());
      }
      // env.statistics->demodulationByRule++;
      TIME_TRACE("demodulation by rule");
      return res;
    }
  }
  return c;
}
