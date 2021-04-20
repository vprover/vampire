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
    pair<Literal*, Literal*> sig;
    bool hyp;
    if (premise->isInductionLiteral(lit, sig, hyp)) {
      // ClauseIterator temp = ClauseIterator::getEmpty();
      // auto it = pvi(pushPairIntoRightIterator(lit,
      //   EqHelper::getEqualityArgumentIterator(lit)));
      // auto it2 = getMapAndFlattenIterator(it, RewriteableSubtermsFn());
      // ClauseIterator inner = pvi(getSingletonIterator(premise));
      // for (unsigned j = 1; j <= lit->_numInductionHypothesis; j++) {
      //   inner = pvi(getMappingIterator(it2, ForwardResultFn(premise, j)));
      // }
      // auto it3 = pvi(getMapAndFlattenIterator(inner, InductResultFn(_splitter, _induction)));
      // res = pvi(getConcatenatedIterator(res, it3));
      ASS(lit->isEquality());
      if (!hyp) {
        for (unsigned k = 0; k <= 1; k++) {
          auto litarg = *lit->nthArgument(k);
          SubtermIterator sti(litarg.term());
          while (sti.hasNext()) {
            auto t = sti.next();
            auto ts = _lhsIndex->getGeneralizations(t);
            while (ts.hasNext()) {
              auto qr = ts.next();
              pair<Literal*, Literal*> sigOther;
              bool hypOther = false;
              bool ind = qr.clause->isInductionLiteral(qr.literal, sigOther, hypOther);
              if (!ind || !hypOther || sig != sigOther) {
                continue;
              }
              Clause* newClause = perform(premise, lit, litarg, t, qr.clause, qr.literal, qr.term, qr.substitution, true);
              ASS(newClause);
              newClause->setStore(Clause::ACTIVE);
              if (_splitter) {
                _splitter->onNewClause(newClause);
              }
              res = pvi(getConcatenatedIterator(res, _induction->generateClauses(newClause)));
              newClause->setStore(Clause::NONE);
            }
          }
        }
      } else {
        for (unsigned j = 0; j <= 1; j++) {
          auto litarg = *lit->nthArgument(j);
          auto ts = _stIndex->getInstances(litarg);
          while (ts.hasNext()) {
            auto qr = ts.next();
            pair<Literal*, Literal*> sigOther;
            bool hypOther = false;
            bool ind = qr.clause->isInductionLiteral(qr.literal, sigOther, hypOther);
            if (!ind || hypOther || sig != sigOther) {
              continue;
            }
            for (unsigned k = 0; k <= 1; k++) {
              auto side = *qr.literal->nthArgument(k);
              if (!side.containsSubterm(qr.term)) {
                continue;
              }
              Clause* newClause = perform(qr.clause, qr.literal, side, qr.term, premise, lit, litarg, qr.substitution, false);
              ASS(newClause);
              newClause->setStore(Clause::ACTIVE);
              if (_splitter) {
                _splitter->onNewClause(newClause);
              }
              res = pvi(getConcatenatedIterator(res, _induction->generateClauses(newClause)));
              newClause->setStore(Clause::NONE);
            }
          }
        }
      }
    }
  }
  return res;
}

Clause *InductionHypothesisRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwSide, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionHypothesisRewriting::perform");
  // the rwClause may not be active as
  // it is from a demodulation index
  // if (rwClause->store() != Clause::ACTIVE) {
  //   return 0;
  // }
  ASS(eqClause->store() == Clause::ACTIVE);

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  TermList tgtTermS;
  if ((eqIsResult && !subst->isIdentityOnQueryWhenResultBound()) || (!eqIsResult && !subst->isIdentityOnResultWhenQueryBound())) {
    //When we apply substitution to the rhs, we get a term, that is
    //a variant of the term we'd like to get, as new variables are
    //produced in the substitution application.
    TermList lhsSBadVars = subst->apply(eqLHS, eqIsResult);
    TermList rhsSBadVars = subst->apply(tgtTerm, eqIsResult);
    Renaming rNorm, qNorm, qDenorm;
    rNorm.normalizeVariables(lhsSBadVars);
    qNorm.normalizeVariables(tgtTerm);
    qDenorm.makeInverse(qNorm);
    ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
    tgtTermS = qDenorm.apply(rNorm.apply(rhsSBadVars));
  }
  else {
    tgtTermS = eqIsResult ? subst->applyToBoundResult(tgtTerm) : subst->applyToBoundQuery(tgtTerm);
  }

  TermList rwSideS(EqHelper::replace(rwSide.term(), rwTerm, tgtTermS));
  if (rwSide == rwTerm) {
    rwSideS = tgtTermS;
  }
  Stack<TermList> args;
  args.push(rwSideS);
  args.push(EqHelper::getOtherEqualitySide(rwLit, rwSide));
  Literal *tgtLitS = Literal::create(rwLit, args.begin());

  // cout << "HYP: " << *eqLit << endl
  //      << "SRC: " << eqLHS << endl
  //      << "TGT: " << tgtTerm << endl
  //      << "RWSIDE: " << rwSideS << endl
  //      << "TGTLIT: " << *tgtLitS << endl;

  if (EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::IH_REWRITING, rwClause, eqClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  // static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;
  // tgtLitS->_hasInductionHypothesis = rwLit->_hasInductionHypothesis;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      // if (doSimS) {
      //   curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      // }
      // curr->_hasInductionHypothesis = (*rwClause)[i]->_hasInductionHypothesis;

      if (EqHelper::isEqTautology(curr)) {
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
        if ((eqIsResult && !subst->isIdentityOnQueryWhenResultBound()) || (!eqIsResult && !subst->isIdentityOnResultWhenQueryBound())) {
          // same as above for RHS
          TermList lhsSBadVars = subst->apply(eqLHS, eqIsResult);
          Literal *currSBadVars = subst->apply(curr, eqIsResult);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(curr);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(tgtTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  return res;
}
