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
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "FnDefRewriting.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

struct FnDefRewriting::GeneralizationsFn {
  GeneralizationsFn(FnDefHandler *index) : _index(index) {}
  VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>> operator()(pair<Literal *, TermList> arg)
  {
    CALL("FnDefRewriting::GeneralizationsFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second)));
  }

private:
  FnDefHandler *_index;
};

struct FnDefRewriting::RewriteableSubtermsFn {
  RewriteableSubtermsFn() = default;

  VirtualIterator<pair<Literal *, TermList>> operator()(Literal *lit)
  {
    CALL("FnDefRewriting::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi(pushPairIntoRightIterator(lit,
                                         getUniquePersistentIteratorFromPtr(&nvi)));
  }
};

struct FnDefRewriting::ForwardResultFn {
  ForwardResultFn(Clause *cl) : _cl(cl) {}

  Clause* operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("FnDefRewriting::ForwardResultFn()");

    if (_cl->store() != Clause::ACTIVE) {
      return 0;
    }
    TermQueryResult &qr = arg.second;
    bool temp;
    return FnDefRewriting::perform(_cl, arg.first.first, arg.first.second, qr.clause,
                                   qr.literal, qr.term, qr.substitution, true, temp,
                                   Inference(GeneratingInference2(InferenceRule::FNDEF_REWRITING, _cl, qr.clause)));
  }

private:
  Clause *_cl;
};

ClauseIterator FnDefRewriting::generateClauses(Clause *premise)
{
  CALL("FnDefRewriting::generateClauses");

  auto itf1 = premise->getSelectedLiteralIterator();

  // Get an iterator of pairs of selected literals and rewritable subterms
  // of those literals. Here all subterms of a literal are rewritable.
  auto itf2 = getMapAndFlattenIterator(itf1, RewriteableSubtermsFn());

  // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
  // returns a pair with the original pair and the generalization result (includes substitution)
  auto itf3 = getMapAndFlattenIterator(itf2, GeneralizationsFn(env.signature->getFnDefHandler()));

  //Perform forward rewriting
  auto it = pvi(getMappingIterator(itf3, ForwardResultFn(premise)));
  // Remove null elements
  auto it2 = getFilteredIterator(it, NonzeroFn());
  return getTimeCountedIterator(it2, TC_FNDEF_REWRITING);
}

bool FnDefRewriting::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  CALL("FnDefRewriting::perform");

  Ordering& ordering = ForwardSimplificationEngine::_salg->getOrdering();

  static DHSet<TermList> attempted;
  attempted.reset();

  unsigned cLen = cl->length();
  for (unsigned li = 0; li < cLen; li++) {
    Literal* lit = (*cl)[li];
    NonVariableIterator it(lit);
    while (it.hasNext()) {
      TermList trm = it.next();
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }

      bool toplevelCheck = ForwardSimplificationEngine::_salg->getOptions().demodulationRedundancyCheck() &&
        lit->isEquality() && (trm==*lit->nthArgument(0) || trm==*lit->nthArgument(1));

      auto git = env.signature->getFnDefHandler()->getGeneralizations(trm);
      while (git.hasNext()) {
        TermQueryResult qr = git.next();
        if (qr.clause->length() != 1) {
          continue;
        }
        auto rhs = EqHelper::getOtherEqualitySide(qr.literal, qr.term);
        if (Ordering::isGorGEorE(ordering.compare(rhs,qr.term))) {
          continue;
        }
        TermList rhsS;
        if(!qr.substitution->isIdentityOnQueryWhenResultBound()) {
          //When we apply substitution to the rhs, we get a term, that is
          //a variant of the term we'd like to get, as new variables are
          //produced in the substitution application.
          TermList lhsSBadVars=qr.substitution->applyToResult(qr.term);
          TermList rhsSBadVars=qr.substitution->applyToResult(rhs);
          Renaming rNorm, qNorm, qDenorm;
          rNorm.normalizeVariables(lhsSBadVars);
          qNorm.normalizeVariables(trm);
          qDenorm.makeInverse(qNorm);
          ASS_EQ(trm,qDenorm.apply(rNorm.apply(lhsSBadVars)));
          rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
        } else {
          rhsS=qr.substitution->applyToBoundResult(rhs);
        }
        if (toplevelCheck) {
          TermList other=EqHelper::getOtherEqualitySide(lit, trm);
          Ordering::Result tord = ordering.compare(rhsS, other);
          if (tord != Ordering::LESS && tord != Ordering::LESS_EQ) {
            Literal* eqLitS = qr.substitution->applyToBoundResult(qr.literal);
            bool isMax=true;
            for (unsigned li2 = 0; li2 < cLen; li2++) {
              if (li == li2) {
                continue;
              }
              if (ordering.compare(eqLitS, (*cl)[li2]) == Ordering::LESS) {
                isMax=false;
                break;
              }
            }
            if (isMax) {
              continue;
            }
          }
        }
        bool isEqTautology = false;
        auto res = FnDefRewriting::perform(cl, lit, trm, qr.clause, qr.literal, qr.term, qr.substitution, true,
          isEqTautology, Inference(SimplifyingInference2(InferenceRule::FNDEF_DEMODULATION, cl, qr.clause)));
        if (!res && !isEqTautology) {
          continue;
        }
        if (!isEqTautology) {
          replacement = res;
        }
        premises = pvi(getSingletonIterator(qr.clause));
        return true;
      }
    }
  }

  return false;
}

Clause *FnDefRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, bool& isEqTautology, const Inference& inf)
{
  CALL("FnDefRewriting::perform");

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

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    isEqTautology = true;
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Clause *res = new (newLength) Clause(newLength, inf);

  static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (doSimS) {
        curr = EqHelper::replace(curr, rwTerm, tgtTermS);
      }

      if (EqHelper::isEqTautology(curr)) {
        isEqTautology = true;
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
          ASS_EQ(rwTerm, qDenorm.apply(rNorm.apply(lhsSBadVars)));
          currAfter = qDenorm.apply(rNorm.apply(currSBadVars));
        }
        else {
          currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        }

        if (EqHelper::isEqTautology(currAfter)) {
          isEqTautology = true;
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  return res;
}
