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
using namespace Indexing;
using namespace Saturation;

void FnDefRewriting::attach(SaturationAlgorithm *salg)
{
  CALL("FnDefRewriting::attach");

  GeneratingInferenceEngine::attach(salg);
  _subtermIndex = static_cast<DemodulationSubtermIndex *>(
      _salg->getIndexManager()->request(DEMODULATION_SUBTERM_SUBST_TREE));
  _lhsIndex = static_cast<FnDefLHSIndex *>(
      _salg->getIndexManager()->request(FNDEF_LHS_SUBST_TREE));
}

void FnDefRewriting::detach()
{
  CALL("FnDefRewriting::detach");

  _subtermIndex = 0;
  _lhsIndex = 0;
  _salg->getIndexManager()->release(DEMODULATION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(FNDEF_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

struct FnDefRewriting::InstancesFn {
  InstancesFn(TermIndex *index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>>);
  OWN_RETURN_TYPE operator()(pair<Literal *, TermList> arg)
  {
    CALL("FnDefRewriting::InstancesFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getInstances(arg.second, true)));
  }

private:
  TermIndex *_index;
};

struct FnDefRewriting::GeneralizationsFn {
  GeneralizationsFn(TermIndex *index) : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>>);
  OWN_RETURN_TYPE operator()(pair<Literal *, TermList> arg)
  {
    CALL("FnDefRewriting::GeneralizationsFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second, true)));
  }

private:
  TermIndex *_index;
};

struct FnDefRewriting::RewriteableSubtermsFn {
  RewriteableSubtermsFn() = default;

  DECL_RETURN_TYPE(VirtualIterator<pair<Literal *, TermList>>);
  OWN_RETURN_TYPE operator()(Literal *lit)
  {
    CALL("FnDefRewriting::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi(pushPairIntoRightIterator(lit,
                                         getUniquePersistentIteratorFromPtr(&nvi)));
  }
};

struct FnDefRewriting::ForwardResultFn {
  ForwardResultFn(Clause *cl) : _cl(cl) {}
  DECL_RETURN_TYPE(Clause *);
  OWN_RETURN_TYPE operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("FnDefRewriting::ForwardResultFn()");

    TermQueryResult &qr = arg.second;
    return FnDefRewriting::perform(_cl, arg.first.first, arg.first.second, qr.clause,
                                   qr.literal, qr.term, qr.substitution, true);
  }

private:
  Clause *_cl;
};

struct FnDefRewriting::BackwardResultFn {
  BackwardResultFn(Clause *cl) : _cl(cl) {}
  DECL_RETURN_TYPE(Clause *);
  OWN_RETURN_TYPE operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("FnDefRewriting::BackwardResultFn()");

    if (_cl == arg.second.clause) {
      return 0;
    }

    TermQueryResult &qr = arg.second;
    return FnDefRewriting::perform(qr.clause, qr.literal, qr.term, _cl, arg.first.first,
                                   arg.first.second, qr.substitution, false);
  }

private:
  Clause *_cl;
};

ClauseIterator FnDefRewriting::generateClauses(Clause *premise)
{
  CALL("FnDefRewriting::generateClauses");

  // forward direction
  ClauseIterator it;
  if (!premise->containsFunctionDefinition()) {
    auto itf1 = premise->getSelectedLiteralIterator();

    // Get an iterator of pairs of selected literals and rewritable subterms
    // of those literals. Here all subterms of a literal are rewritable.
    auto itf2 = getMapAndFlattenIterator(itf1, RewriteableSubtermsFn());

    // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
    // returns a pair with the original pair and the generalization result (includes substitution)
    auto itf3 = getMapAndFlattenIterator(itf2, GeneralizationsFn(_lhsIndex));

    //Perform forward rewriting
    it = pvi(getMappingIterator(itf3, ForwardResultFn(premise)));
  }
  // backward direction
  else {
    // The selected literal is the only one marked as a function definition,
    // all other literals are conditions which are dealt with after this rewriting
    Literal *selected = nullptr;
    for (unsigned i = 0; i < premise->length(); i++) {
      auto lit = (*premise)[i];
      if (premise->isFunctionDefinition(lit)) {
        ASS(!selected);
        selected = lit;
      }
    }
    auto itb1 = pvi(pushPairIntoRightIterator(selected,
                                              EqHelper::getFnDefLHSIterator(selected, premise->isReversedFunctionDefinition(selected))));
    auto itb2 = getMapAndFlattenIterator(itb1, InstancesFn(_subtermIndex));

    //Perform backward rewriting
    it = pvi(getMappingIterator(itb2, BackwardResultFn(premise)));
  }
  // Remove null elements
  auto it2 = getFilteredIterator(it, NonzeroFn());
  return getTimeCountedIterator(it2, TC_FNDEF_REWRITING);
}

Clause *FnDefRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("FnDefRewriting::perform");
  // the rwClause may not be active as
  // it is from a demodulation index
  if (rwClause->store() != Clause::ACTIVE) {
    return 0;
  }
  ASS(eqClause->store() == Clause::ACTIVE);

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());
  ASS(!rwClause->containsFunctionDefinition());

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
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::FNDEF_REWRITING, rwClause, eqClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  static bool doSimS = env.options->simulatenousSuperposition();
  (*res)[0] = tgtLitS;
  tgtLitS->_hasInductionHypothesis = rwLit->_hasInductionHypothesis;
  // rwLit->_hasInductionHypothesis = false;
  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      if (doSimS) {
        curr = EqHelper::replace(curr, rwTerm, tgtTermS);
        curr->_hasInductionHypothesis = (*rwClause)[i]->_hasInductionHypothesis;
        // (*rwClause)[i]->_hasInductionHypothesis = false;
      }

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
