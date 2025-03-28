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
 * @file SubVarSup.cpp
 * Implements class SubVarSup.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "SubVarSup.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using std::pair;

void SubVarSup::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SubVarSupSubtermIndex*> (
	  _salg->getIndexManager()->request(SUB_VAR_SUP_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<SubVarSupLHSIndex*> (
	  _salg->getIndexManager()->request(SUB_VAR_SUP_LHS_SUBST_TREE) );
}

void SubVarSup::detach()
{
  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUB_VAR_SUP_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(SUB_VAR_SUP_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}
  


struct SubVarSup::RewritableResultsFn
{
  RewritableResultsFn(SubVarSupSubtermIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TypedTermList>, QueryRes<ResultSubstitutionSP, TermLiteralClause>> > operator()(pair<Literal*, TypedTermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, /* retrieveSubstitutions */ true)) );
  }
private:
  SubVarSupSubtermIndex* _index;
};

struct SubVarSup::RewriteableSubtermsFn
{
  RewriteableSubtermsFn(Ordering& ord, Clause* prem) : _ord(ord) { 
    prem->collectUnstableVars(_unstableVars);
  }

  VirtualIterator<pair<Literal*, TypedTermList> > operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, EqHelper::getRewritableVarsIterator(&_unstableVars, lit, _ord)) );
  }

private:
  DHSet<unsigned> _unstableVars;
  Ordering& _ord;
};

struct SubVarSup::ApplicableRewritesFn
{
  ApplicableRewritesFn(SubVarSupLHSIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TypedTermList>, QueryRes<ResultSubstitutionSP, TermLiteralClause>> > operator()(pair<Literal*, TypedTermList> arg)
  {
    return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, /* retrieveSubst */ false)) );
  }
private:
  SubVarSupLHSIndex* _index;
};


struct SubVarSup::ForwardResultFn
{
  ForwardResultFn(Clause* cl, SubVarSup& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg)
  {
    QueryRes<ResultSubstitutionSP, TermLiteralClause>& qr = arg.second;
    return _parent.performSubVarSup(_cl, arg.first.first, arg.first.second,
	    qr.data->clause, qr.data->literal, qr.data->term, true);
  }
private:
  Clause* _cl;
  SubVarSup& _parent;
};


struct SubVarSup::BackwardResultFn
{
  BackwardResultFn(Clause* cl, SubVarSup& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg)
  {

    if(_cl==arg.second.data->clause) {
      return 0;
    }

    QueryRes<ResultSubstitutionSP, TermLiteralClause>& qr = arg.second;
    return _parent.performSubVarSup(qr.data->clause, qr.data->literal, qr.data->term,
	    _cl, arg.first.first, arg.first.second, false);
  }
private:
  Clause* _cl;
  SubVarSup& _parent;
};

struct SubVarSup::PotentialApplicationIters {
  SubVarSup& self;

  auto iterFwd(Clause* premise, Literal* lit) {
    // Get an iterator of pairs of selected literals and rewritable subterms of those literals
    // A subterm is rewritable (see EqHelper) if
    //  a) The literal is a positive equality t1=t2 and the subterm is max(t1,t2) wrt ordering
    //  b) The subterm is not a variable
    return iterTraits(SubVarSup::RewriteableSubtermsFn(self._salg->getOrdering(), premise)(lit))

    // Get clauses with a literal whose complement unifies with the rewritable subterm,
    // returns a pair with the original pair and the unification result (includes substitution)
       .flatMap(SubVarSup::ApplicableRewritesFn(self._lhsIndex));
  }


  auto iterBwd(Clause* premise, Literal* lit) {
    return iterTraits(EqHelper::SubVarSupLHSIteratorFn(self._salg->getOrdering())(lit))
             .flatMap(SubVarSup::RewritableResultsFn(self._subtermIndex));
  }

};


VirtualIterator<std::tuple<>> SubVarSup::lookaheadResultEstimation(SelectedAtom const& selection) {
  return pvi(concatIters(
        dropElementType(PotentialApplicationIters{*this}.iterFwd(selection.clause(), selection.literal())),
        dropElementType(PotentialApplicationIters{*this}.iterBwd(selection.clause(), selection.literal()))
  ));
}

ClauseIterator SubVarSup::generateClauses(Clause* premise)
{

  auto itf = iterTraits(premise->getSelectedLiteralIterator())
    .flatMap([=](auto l) { return PotentialApplicationIters{*this}.iterFwd(premise, l); })
  //Perform forward SubVarSup
     .map(ForwardResultFn(premise, *this));

  auto itb = iterTraits(premise->getSelectedLiteralIterator())
            .flatMap([=](auto l) { return PotentialApplicationIters{*this}.iterBwd(premise, l); })
  //Perform backward SubVarSup
             .map(BackwardResultFn(premise, *this));

  // Add the results of forward and backward together
  return pvi(concatIters(std::move(itf),std::move(itb))
  // Remove null elements - these can come from performSubVarSup
          .filter(NonzeroFn()));
}


/**
 * If SubVarSup should be performed, return result of the SubVarSup,
 * otherwise return 0.
 */
Clause* SubVarSup::performSubVarSup(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS, bool eqIsResult)
{
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);
  ASS(rwTerm.isVar());

  //cout << "performSubVarSup with " << rwClause->toString() << " and " << eqClause->toString() << endl;
  //cout << "rwTerm " << rwTerm.toString() << " eqLHSS " << eqLHS.toString() << endl;

  static RobSubstitution subst;
  subst.reset();
  
  TermList freshVar = TermList(Int::max(rwClause->maxVar(), eqClause->maxVar()) + 1, false);

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();

  int newAge=Int::max(rwClause->age(),eqClause->age())+1; // TODO isn't this set automatically?

  Literal* rwLitS = subst.apply(rwLit, 0);
  TermList rwTermS = subst.apply(rwTerm, 0);
  Literal* eqLitS = subst.apply(eqLit, 1);
  TermList eqLHSS = subst.apply(eqLHS, 1);
  TermList freshVarS = subst.apply(freshVar, 0); 

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLitS, eqLHSS);

  auto varSort = SortHelper::getEqualityArgumentSort(eqLitS);
  TermList eqSort = SortHelper::getEqualityArgumentSort(eqLitS);
  
  TermList newEqLHS = ApplicativeHelper::createAppTerm(eqSort, varSort, freshVarS, eqLHSS);
  TermList newTgtTm = ApplicativeHelper::createAppTerm(eqSort, varSort, freshVarS, tgtTerm);

  //ALWAYS(subst.unify(varSort, 0, varSort, 1));
  //ALWAYS(subst.unify(rwTerm, 0, newEqLHS, 1));

  Ordering& ordering = _salg->getOrdering();

  //Literal* rwLitS = subst.apply(rwLit, 0);
  //TermList rwTermS = subst.apply(rwTerm, 0);
  //newEqLHS = subst.apply(newEqLHS, 1);
  ///newTgtTm = subst.apply(newTgtTm, 1);

#if VDEBUG
   //ASS_EQ(rwTermS,newEqLHS);
#endif

  //cout << "Check ordering on " << tgtTermS.toString() << " and " << rwTermS.toString() << endl;

  /*if(rwLitS->isEquality()) {
    //check that we're not rewriting only the smaller side of an equality
    TermList arg0=*rwLitS->nthArgument(0);
    TermList arg1=*rwLitS->nthArgument(1);

    if(!arg0.containsSubterm(rwTermS)) {
      if(Ordering::isGreaterOrEqual(ordering.getEqualityArgumentOrder(rwLitS))) {
        return 0;
      }
    } else if(!arg1.containsSubterm(rwTermS)) {
      if(Ordering::isGreaterOrEqual(Ordering::reverse(ordering.getEqualityArgumentOrder(rwLitS)))) {
        return 0;
      }
    }
  }*/

  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,newTgtTm);

  //check we don't create an equational tautology (this happens during self-SubVarSup)
  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();

  Inference inf(GeneratingInference2(InferenceRule::SUB_VAR_SUP, rwClause, eqClause));
  RStack<Literal*> resLits;

  resLits->push(tgtLitS);
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr = (*rwClause)[i];
    if(curr!=rwLit) {
      Literal* currAfter = subst.apply(curr, 0);
      currAfter = EqHelper::replace(currAfter,rwTermS,newEqLHS);

      if(EqHelper::isEqTautology(currAfter)) {
        return nullptr;
      }
      
      if (afterCheck) {
        TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
        if (i < rwClause->numSelected() && ordering.compare(currAfter,rwLitS) == Ordering::GREATER) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          return nullptr;
        }
      }

      resLits->push(currAfter);
    }
  }


  for(unsigned i=0;i<eqLength;i++) {
    Literal* curr=(*eqClause)[i];
    if(curr!=eqLit) {
      Literal* currAfter = subst.apply(curr, 1);

      if(EqHelper::isEqTautology(currAfter)) {
        return nullptr;
      }

      resLits->push(currAfter);
    }
  } //no need for after check as no variables in D are bound to anyhting
    //the most that is happenning is a rearrangement of vars in D
  

  
  if(rwClause==eqClause) {
    env.statistics->selfSubVarSup++;
  } else if(eqIsResult) {
    env.statistics->forwardSubVarSup++;
  } else {
    env.statistics->backwardSubVarSup++;
  }

  //cout << "SUBVARSUP " + res->toString() << endl;
  auto res = Clause::fromStack(*resLits, inf);
  res->setAge(newAge);
  return res;
}
