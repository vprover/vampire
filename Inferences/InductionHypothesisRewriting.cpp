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

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"

#include "InductionHypothesisRewriting.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;

ClauseIterator InductionHypothesisRewriting::generateClauses(Clause *premise)
{
  CALL("InductionHypothesisRewriting::generateClauses");

  ClauseIterator res = ClauseIterator::getEmpty();
  for (unsigned i = 0; i < premise->length(); i++) {
    auto lit = (*premise)[i];
    if (lit->isEquality() && lit->_inductionHypotheses != nullptr) {
      // cout << *lit << " has induction hypotheses: ";
      List<Literal*>::Iterator ihIt(lit->_inductionHypotheses);
      while (ihIt.hasNext()) {
        auto ih = ihIt.next();
        // cout << *ih << " ";
        for (unsigned i = 0; i <= 1; i++) {
          auto litarg = *lit->nthArgument(i);
          SubtermIterator sti(litarg.term());
          while (sti.hasNext()) {
            auto t = sti.next();
            for (unsigned j = 0; j <= 1; j++) {
              TermList iarg = *ih->nthArgument(j);
              RobSubstitutionSP subst(new RobSubstitution);
              if (subst->match(iarg, 0, t, 1)) {
                Clause* newClause = perform(premise, lit, litarg, t, 0, ih, iarg, subst);
                newClause->setStore(Clause::ACTIVE);
                if (_splitter) {
                  _splitter->onNewClause(newClause);
                }
                // cout << "IH rewriting: " << *premise << endl
                //   << " with " << *ih << endl
                //   << " results " << *newClause << endl;
                res = pvi(getConcatenatedIterator(res, _induction->generateClauses(newClause)));
                newClause->setStore(Clause::NONE);
              }
            }
          }
        }
      }
      // cout << endl;
    }
  }
  return res;
}

Clause *InductionHypothesisRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwSide, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS, RobSubstitutionSP subst)
{
  CALL("InductionHypothesisRewriting::perform");
  // the rwClause may not be active as
  // it is from a demodulation index
  if (rwClause->store() != Clause::ACTIVE) {
    return 0;
  }
  // ASS(eqClause->store() == Clause::ACTIVE);

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  // cout << "HYP: " << *eqLit << endl
  //      << "SRC: " << eqLHS << endl
  //      << "TGT: " << tgtTerm << endl;
  if (!tgtTerm.containsAllVariablesOf(rwTerm)) {
    cout << "there are unbound variables in IH rhs" << endl;
    return 0;
  }
  TermList tgtTermS = subst->apply(tgtTerm, 0);

  TermList rwSideS(EqHelper::replace(rwSide.term(), rwTerm, tgtTermS));
  Stack<TermList> args;
  args.push(rwSideS);
  args.push(EqHelper::getOtherEqualitySide(rwLit, rwSide));
  Literal *tgtLitS = Literal::create(rwLit, args.begin());
  if (EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }
  // cout << "TGT applied: " << tgtTermS << endl
  //      << "CONC: " << *tgtLitS << endl;

  unsigned rwLength = rwClause->length();
  // unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength /*+ eqLength*/;

  Inference inf(GeneratingInference2(InferenceRule::IH_REWRITING, rwClause, rwClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  // static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      // if (doSimS) {
      //   curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      // }

      if (EqHelper::isEqTautology(curr)) {
        res->destroy();
        return 0;
      }

      (*res)[next++] = curr;
    }
  }

  // {
  //   for (unsigned i = 0; i < eqLength; i++) {
  //     Literal *curr = (*eqClause)[i];
  //     if (curr != eqLit) {
  //       Literal *currAfter;
  //       if ((eqIsResult && !subst->isIdentityOnQueryWhenResultBound()) || (!eqIsResult && !subst->isIdentityOnResultWhenQueryBound())) {
  //         // same as above for RHS
  //         TermList lhsSBadVars = subst->apply(eqLHS, eqIsResult);
  //         Literal *currSBadVars = subst->apply(curr, eqIsResult);
  //         Renaming rNorm, qNorm, qDenorm;
  //         rNorm.normalizeVariables(lhsSBadVars);
  //         qNorm.normalizeVariables(curr);
  //         qDenorm.makeInverse(qNorm);
  //         ASS_EQ(tgtTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
  //         currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
  //       }
  //       else {
  //         currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
  //       }

  //       if (EqHelper::isEqTautology(currAfter)) {
  //         res->destroy();
  //         return 0;
  //       }

  //       (*res)[next++] = currAfter;
  //     }
  //   }
  // }

  return res;
}
