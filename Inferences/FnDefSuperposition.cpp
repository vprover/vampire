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
 * @file FnDefSuperposition.cpp
 * Implements class FnDefSuperposition.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/LiteralSelector.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "FnDefSuperposition.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void FnDefSuperposition::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SuperpositionSubtermIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<FnDefLHSIndex*> (
	  _salg->getIndexManager()->request(FNDEF_LHS_SUBST_TREE) );
}

void FnDefSuperposition::detach()
{
  CALL("Superposition::detach");

  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(FNDEF_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}

struct FnDefSuperposition::UnificationsFn
{
  UnificationsFn(TermIndex* index,bool wc) : _index(index),_withC(wc) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    CALL("FnDefSuperposition::UnificationsFn()");
    if(_withC){
      return pvi( pushPairIntoRightIterator(arg, _index->getUnificationsWithConstraints(arg.second, true)) );
    }
    else{
      return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
    }
  }
private:
  TermIndex* _index;
  bool _withC;
};

struct FnDefSuperposition::RewriteableSubtermsFn
{
  RewriteableSubtermsFn() = default;

  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    CALL("Superposition::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi( pushPairIntoRightIterator(lit,
      getUniquePersistentIteratorFromPtr(&nvi)) );
  }
};

struct FnDefSuperposition::ForwardResultFn
{
  ForwardResultFn(Clause* cl, FnDefSuperposition& parent) : _cl(cl), _parent(parent) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return _parent.performSuperposition(_cl, arg.first.first, arg.first.second,
	    qr.clause, qr.literal, qr.term, qr.substitution, true, qr.constraints);
  }
private:
  Clause* _cl;
  FnDefSuperposition& _parent;
};


struct FnDefSuperposition::BackwardResultFn
{
  BackwardResultFn(Clause* cl, FnDefSuperposition& parent) : _cl(cl), _parent(parent) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::BackwardResultFn::operator()");

    if(_cl==arg.second.clause) {
      return 0;
    }

    TermQueryResult& qr = arg.second;
    return _parent.performSuperposition(qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, qr.constraints);
  }
private:
  Clause* _cl;
  FnDefSuperposition& _parent;
};


ClauseIterator FnDefSuperposition::generateClauses(Clause* premise)
{
  CALL("Superposition::generateClauses");

  //cout << "SUPERPOSITION with " << premise->toString() << endl;

  //TODO probably shouldn't go here!
  static bool withConstraints = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;

  if (!premise->containsFunctionDefinition()) {
    auto itf1 = premise->getSelectedLiteralIterator();

    // Get an iterator of pairs of selected literals and rewritable subterms of those literals
    // A subterm is rewritable (see EqHelper) if it is a non-variable subterm of either
    // a maximal side of an equality or of a non-equational literal
    auto itf2 = getMapAndFlattenIterator(itf1,RewriteableSubtermsFn());

    // Get clauses with a literal whose complement unifies with the rewritable subterm,
    // returns a pair with the original pair and the unification result (includes substitution)
    auto itf3 = getMapAndFlattenIterator(itf2,UnificationsFn(_lhsIndex,withConstraints));

    //Perform forward superposition
    auto itf4 = getMappingIterator(itf3,ForwardResultFn(premise, *this));

    // Remove null elements - these can come from performSuperposition
    auto it6 = getFilteredIterator(itf4,NonzeroFn());

    // The outer iterator ensures we update the time counter for superposition
    auto it7 = getTimeCountedIterator(it6, TC_SUPERPOSITION);

    return pvi( it7 );
  } else {

    Literal* selected = nullptr;
    for (unsigned i = 0; i < premise->length(); i++) {
      auto lit = (*premise)[i];
      if (premise->isFunctionDefinition(lit)) {
        ASS(!selected);
        selected = lit;
      }
    }
    auto itb1 = pvi( pushPairIntoRightIterator(selected,
      EqHelper::getFnDefLHSIterator(selected, premise->isReversedFunctionDefinition(selected))) );
    auto itb2 = getMapAndFlattenIterator(itb1,UnificationsFn(_subtermIndex,withConstraints));

    //Perform backward superposition
    auto itb4 = getMappingIterator(itb2,BackwardResultFn(premise, *this));

    // Remove null elements - these can come from performSuperposition
    auto it6 = getFilteredIterator(itb4,NonzeroFn());

    // The outer iterator ensures we update the time counter for superposition
    auto it7 = getTimeCountedIterator(it6, TC_SUPERPOSITION);

    return pvi( it7 );
  }
}

/**
 * If superposition should be performed, return result of the superposition,
 * otherwise return 0.
 */
Clause* FnDefSuperposition::performSuperposition(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult,
    UnificationConstraintStackSP constraints)
{
  CALL("Superposition::performSuperposition");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);
  // cout << "superposition " << *eqClause << " " << rwClause->containsFunctionDefinition() << " " << *rwClause << endl;

  //cout << "performSuperposition with " << rwClause->toString() << " and " << eqClause->toString() << endl;
  //cout << "rwTerm " << rwTerm.toString() << " eqLHSS " << eqLHS.toString() << endl;

  // the first checks the reference and the second checks the stack
/*
  if(!constraints.isEmpty() && !constraints->isEmpty()){ 
    cout << "has constraints" << endl; 
    Stack<UnificationConstraint>::Iterator uit(*constraints);
    while(uit.hasNext()){ auto c = uit.next(); cout << c.first.toString() << "," << c.second.toString() << endl; }
  }
  cout << "subst " << endl << subst->toString() << endl;
*/

  // the first checks the reference and the second checks the stack
  bool hasConstraints = !constraints.isEmpty() && !constraints->isEmpty();
  unsigned sort = SortHelper::getEqualityArgumentSort(eqLit);

  if(SortHelper::getTermSort(rwTerm, rwLit)!=sort) {
    //cannot perform superposition because sorts don't match
    return 0;
  }

  ASS(!eqLHS.isVar());
  ASS(!rwClause->containsFunctionDefinition());

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned conLength = hasConstraints ? constraints->size() : 0;

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  // LRS-specific optimization:
  // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
  // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
  // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.

  unsigned numPositiveLiteralsLowerBound = Int::max(eqClause->numPositiveLiterals()-1, rwClause->numPositiveLiterals()); // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur

  Inference inf(GeneratingInference2(hasConstraints ? InferenceRule::CONSTRAINED_SUPERPOSITION : InferenceRule::FNDEF_SUPERPOSITION, rwClause, eqClause));
  Inference::Destroyer inf_destroyer(inf);

  Ordering& ordering = _salg->getOrdering();

  TermList eqLHSS = subst->apply(eqLHS, eqIsResult);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);

  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);

#if VDEBUG
  if(!hasConstraints){
    ASS_EQ(rwTermS,eqLHSS);
  }
#endif

  //cout << "Check ordering on " << tgtTermS.toString() << " and " << rwTermS.toString() << endl;

  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,tgtTermS);

  static bool doSimS = getOptions().simulatenousSuperposition();

  //check we don't create an equational tautology (this happens during self-superposition)
  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned newLength = rwLength+eqLength-1+conLength;

  static bool afterCheck = getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete();

  inf_destroyer.disable(); // ownership passed to the the clause below
  Clause* res = new(newLength) Clause(newLength, inf);

  // If proof extra is on let's compute the positions we have performed
  // superposition on 
  if(env.options->proofExtra()==Options::ProofExtra::FULL){
    /*
    cout << "rwClause " << rwClause->toString() << endl;
    cout << "eqClause " << eqClause->toString() << endl;
    cout << "rwLit " << rwLit->toString() << endl;
    cout << "eqLit " << eqLit->toString() << endl;
    cout << "rwTerm " << rwTerm.toString() << endl;
    cout << "eqLHS " << eqLHS.toString() << endl;
     */
    //cout << subst->toString() << endl;

    // First find which literal it is in the clause, as selection has occured already
    // this should remain the same...?
    vstring rwPlace = Lib::Int::toString(rwClause->getLiteralPosition(rwLit));
    vstring eqPlace = Lib::Int::toString(eqClause->getLiteralPosition(eqLit));

    vstring rwPos="_";
    ALWAYS(Kernel::positionIn(rwTerm,rwLit,rwPos));
    vstring eqPos = "("+eqPlace+").2";
    rwPos = "("+rwPlace+")."+rwPos;

    vstring eqClauseNum = Lib::Int::toString(eqClause->number());
    vstring rwClauseNum = Lib::Int::toString(rwClause->number());

    vstring extra = eqClauseNum + " into " + rwClauseNum+", unify on "+
        eqPos+" in "+eqClauseNum+" and "+
        rwPos+" in "+rwClauseNum;

    //cout << extra << endl;
    //NOT_IMPLEMENTED;

    if (!env.proofExtra) {
      env.proofExtra = new DHMap<void*,vstring>();
    }
    env.proofExtra->insert(res,extra);
  }

  (*res)[0] = tgtLitS;
  int next = 1;
  unsigned weight=tgtLitS->weight();
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit) {
      Literal* currAfter = subst->apply(curr, !eqIsResult);

      if (doSimS) {
        currAfter = EqHelper::replace(currAfter,rwTermS,tgtTermS);
      }

      if(EqHelper::isEqTautology(currAfter)) {
        goto construction_fail;
      }

      if (afterCheck) {
        TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
        if (i < rwClause->numSelected() && ordering.compare(currAfter,rwLitS) == Ordering::GREATER) {
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          goto construction_fail;
        }
      }

      (*res)[next++] = currAfter;
    }
  }

  {
    Literal* eqLitS = 0;
    if (afterCheck && eqClause->numSelected() > 1) {
      TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
      eqLitS = Literal::createEquality(true,eqLHSS,tgtTermS,sort);
    }

    for(unsigned i=0;i<eqLength;i++) {
      Literal* curr=(*eqClause)[i];
      if(curr!=eqLit) {
        Literal* currAfter = subst->apply(curr, eqIsResult);

        if(EqHelper::isEqTautology(currAfter)) {
          goto construction_fail;
        }

        if (eqLitS && i < eqClause->numSelected()) {
          TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);

          Ordering::Result o = ordering.compare(currAfter,eqLitS);

          if (o == Ordering::GREATER || o == Ordering::GREATER_EQ || o == Ordering::EQUAL) { // where is GREATER_EQ ever coming from?
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            goto construction_fail;
          }
        }

        (*res)[next++] = currAfter;
      }
    }
  }
  if(hasConstraints){
    for(unsigned i=0;i<constraints->size();i++){
      pair<pair<TermList,unsigned>,pair<TermList,unsigned>> con = (*constraints)[i];

      TermList qT = subst->applyTo(con.first.first,con.first.second);
      TermList rT = subst->applyTo(con.second.first,con.second.second);

      unsigned sort = SortHelper::getResultSort(rT.term());
      Literal* constraint = Literal::createEquality(false,qT,rT,sort);

      static Options::UnificationWithAbstraction uwa = env.options->unificationWithAbstraction();
      if(uwa==Options::UnificationWithAbstraction::GROUND && 
         !constraint->ground() &&
         (!theory->isInterpretedFunction(qT) && !theory->isInterpretedConstant(qT)) &&
         (!theory->isInterpretedFunction(rT) && !theory->isInterpretedConstant(rT))){

        // the unification was between two uninterpreted things that were not ground 
        res->destroy();
        return 0;
      }

      (*res)[next] = constraint;
      next++;   
    }
  }

  if(false) {
    construction_fail:
    res->destroy();
    return 0;
  }

  if(!hasConstraints){
    if(rwClause==eqClause) {
      env.statistics->selfSuperposition++;
    } else if(eqIsResult) {
      env.statistics->forwardSuperposition++;
    } else {
      env.statistics->backwardSuperposition++;
    }
  } else {
    if(rwClause==eqClause) {
      env.statistics->cSelfSuperposition++;
    } else if(eqIsResult) {
      env.statistics->cForwardSuperposition++;
    } else {
      env.statistics->cBackwardSuperposition++;
    }
  }

/*
  if(hasConstraints){ 
    cout << "RETURNING " << res->toString() << endl;
    //NOT_IMPLEMENTED;
  }
*/

  return res;
}
