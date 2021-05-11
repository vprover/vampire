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
    res = pvi(getConcatenatedIterator(res, generateClauses((*premise)[i], premise)));
  }
  return res;
}

ClauseIterator InductionHypothesisRewriting::generateClauses(Literal* lit, Clause *premise)
{
  ClauseIterator res = ClauseIterator::getEmpty();
  if (!lit->isEquality()) {
    return res;
  }
  vset<unsigned> sig;
  bool hyp, rev;
  if (premise->isInductionLiteral(lit, sig, hyp, rev)) {
    static const bool fixSides = env.options->inductionHypRewritingFixSides();
    if (!hyp) {
      for (unsigned k = 0; k <= 1; k++) {
        auto litarg = *lit->nthArgument(k);
        NonVariableIterator sti(litarg.term(), true);
        while (sti.hasNext()) {
          auto t = sti.next();
          auto ts = _lhsIndex->getGeneralizations(t);
          while (ts.hasNext()) {
            auto qr = ts.next();
            vset<unsigned> sigOther;
            bool hypOther = false, revOther;
            bool ind = qr.clause->isInductionLiteral(qr.literal, sigOther, hypOther, revOther);
            if (!ind || !hypOther) {
              continue;
            }
            ASS(sigOther.size() == 1);
            unsigned sigUsed = *sigOther.begin();
            if (!sig.count(sigUsed)) {
              continue;
            }
            if (fixSides && (qr.term == *qr.literal->nthArgument(k)) != (rev == revOther)) {
              continue;
            }
            res = pvi(getConcatenatedIterator(res,
              perform(sigUsed, premise, lit, litarg, t, qr.clause, qr.literal, qr.term, qr.substitution, true)));
          }
        }
      }
    } else if (lit->isPositive()) {
      ASS(sig.size() == 1);
      unsigned sigUsed = *sig.begin();
      static const bool ordered = env.options->inductionHypRewritingOrdered();
      TermIterator lhsi;
      if (ordered) {
        lhsi = EqHelper::getLHSIterator(lit, _salg->getOrdering());
      } else {
        lhsi = EqHelper::getEqualityArgumentIterator(lit);
      }
      while (lhsi.hasNext()) {
        TermList lhs = lhsi.next();
        TermList litarg = EqHelper::getOtherEqualitySide(lit, lhs);
        auto ts = _stIndex->getInstances(litarg);
        while (ts.hasNext()) {
          auto qr = ts.next();
          vset<unsigned> sigOther;
          bool hypOther = false, revOther;
          bool ind = qr.clause->isInductionLiteral(qr.literal, sigOther, hypOther, revOther);
          if (!ind || hypOther) {
            continue;
          }
          if (!sigOther.count(sigUsed)) {
            continue;
          }
          for (unsigned k = 0; k <= 1; k++) {
            auto side = *qr.literal->nthArgument(k);
            if (!side.containsSubterm(qr.term)) {
              continue;
            }
            if (fixSides && ((litarg == *lit->nthArgument(1)) == k) != (rev == revOther)) {
              continue;
            }
            res = pvi(getConcatenatedIterator(res,
              perform(sigUsed, qr.clause, qr.literal, side, qr.term, premise, lit, litarg, qr.substitution, false)));
          }
        }
      }
    }
  }
  return res;
}

ClauseIterator InductionHypothesisRewriting::perform(unsigned sig,
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
  ClauseIterator res = ClauseIterator::getEmpty();

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return res;
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
    return res;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::IH_REWRITING, rwClause, eqClause));
  Clause *newCl = new (newLength) Clause(newLength, inf);

  // static bool doSimS = env.options->simulatenousSuperposition();
  (*newCl)[0] = tgtLitS;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      // if (doSimS) {
      //   curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      // }

      if (EqHelper::isEqTautology(curr)) {
        newCl->destroy();
        return res;
      }

      (*newCl)[next++] = curr;
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
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          newCl->destroy();
          return res;
        }

        (*newCl)[next++] = currAfter;
      }
    }
  }

  newCl->setStore(Clause::ACTIVE);
  if (_splitter) {
    _splitter->onNewClause(newCl);
  }
  auto temp = _dupLitRemoval->simplify(newCl);
  if (temp != newCl) {
    if (_splitter) {
      _splitter->onNewClause(newCl);
    }
    newCl->setStore(Clause::NONE);
    newCl = temp;
    newCl->setStore(Clause::ACTIVE);
  }
  newCl->inductionInfo() = new DHMap<Literal*,tuple<vset<unsigned>,bool,bool>>(*rwClause->inductionInfo());
  newCl->inductionInfo()->insert(tgtLitS, newCl->inductionInfo()->get(rwLit));
  get<0>(newCl->inductionInfo()->get(tgtLitS)).erase(sig);
  res = pvi(getConcatenatedIterator(generateClauses(tgtLitS, newCl), _induction->generateClauses(newCl)));
  newCl->setStore(Clause::NONE);

  return res;
}
