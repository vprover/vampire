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
 * @file Superposition.cpp
 * Implements class Superposition.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Set.hpp"

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
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/TermSharing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Superposition.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void Superposition::attach(SaturationAlgorithm* salg)
{
  CALL("Superposition::attach");

  GeneratingInferenceEngine::attach(salg);
  _subtermIndex=static_cast<SuperpositionSubtermIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_SUBTERM_SUBST_TREE) );
  _lhsIndex=static_cast<SuperpositionLHSIndex*> (
	  _salg->getIndexManager()->request(SUPERPOSITION_LHS_SUBST_TREE) );
}

void Superposition::detach()
{
  CALL("Superposition::detach");

  _subtermIndex=0;
  _lhsIndex=0;
  _salg->getIndexManager()->release(SUPERPOSITION_SUBTERM_SUBST_TREE);
  _salg->getIndexManager()->release(SUPERPOSITION_LHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}



struct Superposition::RewritableResultsFn
{
  RewritableResultsFn(SuperpositionSubtermIndex* index,bool wc,bool ea) : _index(index),
                     _withC(wc), _extByAbs(ea) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("Superposition::RewritableResultsFn()");
    if(_withC){
      return pvi( pushPairIntoRightIterator(arg, _index->getUnificationsWithConstraints(arg.second, true)) );
    }
    else if(_extByAbs){
      TermList sort = SortHelper::getTermSort(arg.second, arg.first);
      return pvi( pushPairIntoRightIterator(arg, _index->getUnificationsUsingSorts(arg.second, sort, true)) );
    }
    else{
      return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
    }
  }
private:
  SuperpositionSubtermIndex* _index;
  bool _withC;
  bool _extByAbs;
};

struct Superposition::RewriteableSubtermsFn
{
  RewriteableSubtermsFn(Ordering& ord) : _ord(ord) {}

  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    CALL("Superposition::RewriteableSubtermsFn()");
    TermIterator it = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, _ord) :
                                                      EqHelper::getSubtermIterator(lit, _ord);
    return pvi( pushPairIntoRightIterator(lit, it) );
  }

private:
  Ordering& _ord;
};

struct Superposition::ApplicableRewritesFn
{
  ApplicableRewritesFn(SuperpositionLHSIndex* index, bool wc, bool ea) : _index(index), 
                      _withC(wc), _extByAbs(ea) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("Superposition::ApplicableRewritesFn()");
    if(_withC){
      return pvi( pushPairIntoRightIterator(arg, _index->getUnificationsWithConstraints(arg.second, true)) );
    }  
    else if(_extByAbs){
      TermList sort = SortHelper::getTermSort(arg.second, arg.first);
      return pvi( pushPairIntoRightIterator(arg, _index->getUnificationsUsingSorts(arg.second, sort, true)) );
    }
    else{
      return pvi( pushPairIntoRightIterator(arg, _index->getUnifications(arg.second, true)) );
    }
  }
private:
  SuperpositionLHSIndex* _index;
  bool _withC;
  bool _extByAbs;
};


struct Superposition::ForwardResultFn
{
  ForwardResultFn(Clause* cl, PassiveClauseContainer* passiveClauseContainer, Superposition& parent) : _cl(cl), _passiveClauseContainer(passiveClauseContainer), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return _parent.performSuperposition(_cl, arg.first.first, arg.first.second,
	    qr.clause, qr.literal, qr.term, qr.substitution, true, _passiveClauseContainer, qr.constraints, qr.isTypeSub);
  }
private:
  Clause* _cl;
  PassiveClauseContainer* _passiveClauseContainer;
  Superposition& _parent;
};


struct Superposition::BackwardResultFn
{
  BackwardResultFn(Clause* cl, PassiveClauseContainer* passiveClauseContainer, Superposition& parent) : _cl(cl), _passiveClauseContainer(passiveClauseContainer), _parent(parent) {}
  Clause* operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("Superposition::BackwardResultFn::operator()");

    if(_cl==arg.second.clause) {
      return 0;
    }

    TermQueryResult& qr = arg.second;
    return _parent.performSuperposition(qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, _passiveClauseContainer, qr.constraints, qr.isTypeSub);
  }
private:
  Clause* _cl;
  PassiveClauseContainer* _passiveClauseContainer;
  Superposition& _parent;
};


ClauseIterator Superposition::generateClauses(Clause* premise)
{
  CALL("Superposition::generateClauses");
  PassiveClauseContainer* passiveClauseContainer = _salg->getPassiveClauseContainer();

  //cout << "SUPERPOSITION with " << premise->toString() << endl;

  //TODO probably shouldn't go here!
  static bool withConstraints = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;
  static bool extByAbstraction = (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION)
                               && env.property->higherOrder();

  auto itf1 = premise->getSelectedLiteralIterator();

  // Get an iterator of pairs of selected literals and rewritable subterms of those literals
  // A subterm is rewritable (see EqHelper) if it is a non-variable subterm of either
  // a maximal side of an equality or of a non-equational literal
  auto itf2 = getMapAndFlattenIterator(itf1,RewriteableSubtermsFn(_salg->getOrdering()));

  // Get clauses with a literal whose complement unifies with the rewritable subterm,
  // returns a pair with the original pair and the unification result (includes substitution)
  auto itf3 = getMapAndFlattenIterator(itf2,ApplicableRewritesFn(_lhsIndex,withConstraints, extByAbstraction));

  //Perform forward superposition
  auto itf4 = getMappingIterator(itf3,ForwardResultFn(premise, passiveClauseContainer, *this));

  auto itb1 = premise->getSelectedLiteralIterator();
  auto itb2 = getMapAndFlattenIterator(itb1,EqHelper::SuperpositionLHSIteratorFn(_salg->getOrdering(), _salg->getOptions()));
  auto itb3 = getMapAndFlattenIterator(itb2,RewritableResultsFn(_subtermIndex,withConstraints, extByAbstraction));

  //Perform backward superposition
  auto itb4 = getMappingIterator(itb3,BackwardResultFn(premise, passiveClauseContainer, *this));

  // Add the results of forward and backward together
  auto it5 = getConcatenatedIterator(itf4,itb4);

  // Remove null elements - these can come from performSuperposition
  auto it6 = getFilteredIterator(it5,NonzeroFn());

  // The outer iterator ensures we update the time counter for superposition
  auto it7 = getTimeCountedIterator(it6, TC_SUPERPOSITION);

  return pvi( it7 );
}

/**
 * Return true iff superposition of @c eqClause into @c rwClause can be performed
 * with respect to colors of the clauses. If the inference is not possible, based
 * on the value of relevant options, report the failure, and/or attempt unblocking
 * the clauses.
 *
 * This function also updates the statistics.
 */
bool Superposition::checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause)
{
  CALL("Superposition::checkClauseColorCompatibility");

  if(ColorHelper::compatible(rwClause->color(), eqClause->color())) {
    return true;
  }
  if(getOptions().showBlocked()) {
    env.beginOutput();
    env.out()<<"Blocked superposition of "<<eqClause->toString()<<" into "<<rwClause->toString()<<endl;
    env.endOutput();
  }
  if(getOptions().colorUnblocking()) {
    SaturationAlgorithm* salg = SaturationAlgorithm::tryGetInstance();
    ASS(salg);
    ColorHelper::tryUnblock(rwClause, salg);
    ColorHelper::tryUnblock(eqClause, salg);
  }
  env.statistics->inferencesSkippedDueToColors++;
  return false;
}

/**
 * Return false iff superposition from variable @c eqLHS should not be
 * performed.
 *
 * This function checks that we don't perform superpositions from
 * variables that occur in the remaining part of the clause either in
 * a literal which is not an equality, or in a as an argument of a function.
 * Such situation would mean that there is no ground substitution in which
 * @c eqLHS would be the larger argument of the largest literal.
 */
bool Superposition::checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS)
{
  CALL("Superposition::checkSuperpositionFromVariable");
  ASS(eqLHS.isVar());
  //if we should do rewriting, LHS cannot appear inside RHS
  //ASS_REP(!EqHelper::getOtherEqualitySide(eqLit, eqLHS).containsSubterm(eqLHS), eqLit->toString());

  unsigned clen = eqClause->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*eqClause)[i];
    if(lit==eqLit) {
      continue;
    }
    if(lit->isEquality()) {
      for(unsigned aIdx=0; aIdx<2; aIdx++) {
	TermList arg = *lit->nthArgument(aIdx);
	if(arg.isTerm() && arg.containsSubterm(eqLHS)) {
	  return false;
	}
      }
    }
    else if(lit->containsSubterm(eqLHS)) {
      return false;
    }
  }

  return true;
}

/**
 * If the weight of the superposition result will be greater than
 * @c weightLimit, increase the counter of discarded non-redundant
 * clauses and return false. Otherwise return true.
 *
 * The fact that true is returned doesn't mean that the weight of
 * the resulting clause will not be over the weight limit, just that
 * it cannot be cheaply determined at this time.
 */
bool Superposition::earlyWeightLimitCheck(Clause* eqClause, Literal* eqLit,
      Clause* rwClause, Literal* rwLit, TermList rwTerm, TermList eqLHS, TermList eqRHS,
      ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer, unsigned numPositiveLiteralsLowerBound, const Inference& inf)
{
  CALL("Superposition::earlyWeightLimitCheck");

  unsigned nonInvolvedLiteralWLB=0;//weight lower bound for literals that aren't going to be rewritten

  unsigned rwLength = rwClause->length();
  for(unsigned i=0;i<rwLength;i++) {
    Literal* curr=(*rwClause)[i];
    if(curr!=rwLit) {
      nonInvolvedLiteralWLB+=curr->weight();
    }
  }
  unsigned eqLength = eqClause->length();
  for(unsigned i=0;i<eqLength;i++) {
    Literal* curr=(*eqClause)[i];
    if(curr!=eqLit) {
      nonInvolvedLiteralWLB+=curr->weight();
    }
  }

  //we assume that there will be at least one rewrite in the rwLit
  if(!passiveClauseContainer->fulfilsWeightLimit(nonInvolvedLiteralWLB + eqRHS.weight(), numPositiveLiteralsLowerBound, inf)) {
    env.statistics->discardedNonRedundantClauses++;
    RSTAT_CTR_INC("superpositions weight skipped early");
    return false;
  }

  unsigned lhsSWeight = subst->getApplicationWeight(eqLHS, eqIsResult);
  unsigned rhsSWeight = subst->getApplicationWeight(eqRHS, eqIsResult);
  int rwrBalance = rhsSWeight-lhsSWeight;

  if(rwrBalance>=0) {
    //there must be at least one rewriting, possibly more
    unsigned approxWeight = rwLit->weight()+rwrBalance;
    if(!passiveClauseContainer->fulfilsWeightLimit(nonInvolvedLiteralWLB + approxWeight, numPositiveLiteralsLowerBound, inf)) {
      env.statistics->discardedNonRedundantClauses++;
      RSTAT_CTR_INC("superpositions weight skipped after rewriter weight retrieval");
      return false;
    }
  }
  //if rewrite balance is 0, it doesn't matter how many times we rewrite
  size_t rwrCnt = (rwrBalance==0) ? 0 : rwLit->countSubtermOccurrences(rwTerm);
  if(rwrCnt>1) {
    ASS_GE(rwrCnt, 1);
    unsigned approxWeight = rwLit->weight()+(rwrBalance*rwrCnt);
    if(!passiveClauseContainer->fulfilsWeightLimit(nonInvolvedLiteralWLB + approxWeight, numPositiveLiteralsLowerBound, inf)) {
      env.statistics->discardedNonRedundantClauses++;
      RSTAT_CTR_INC("superpositions weight skipped after rewriter weight retrieval with occurrence counting");
      return false;
    }
  }

  unsigned rwLitSWeight = subst->getApplicationWeight(rwLit, !eqIsResult);

  unsigned finalLitWeight = rwLitSWeight+(rwrBalance*rwrCnt);
  if(!passiveClauseContainer->fulfilsWeightLimit(nonInvolvedLiteralWLB + finalLitWeight, numPositiveLiteralsLowerBound, inf)) {
    env.statistics->discardedNonRedundantClauses++;
    RSTAT_CTR_INC("superpositions weight skipped after rewrited literal weight retrieval");
    return false;
  }

  return true;
}

/**
 * If superposition should be performed, return result of the superposition,
 * otherwise return 0.
 */
Clause* Superposition::performSuperposition(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, PassiveClauseContainer* passiveClauseContainer,
    UnificationConstraintStackSP constraints, bool isTypeSub)
{
  CALL("Superposition::performSuperposition");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  /* cout << "performSuperposition with " << rwClause->toString() << " and " << eqClause->toString() << endl;
    cout << "rwTerm " << rwTerm.toString() << " eqLHS " << eqLHS.toString() << endl;
    cout << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl;
    cout << "eqIsResult " << eqIsResult << endl;*/


  // the first checks the reference and the second checks the stack
/*
  if(!constraints.isEmpty() && !constraints->isEmpty()){ 
    cout << "has constraints" << endl; 
    Stack<UnificationConstraint>::Iterator uit(*constraints);
    while(uit.hasNext()){ auto c = uit.next(); cout << c.first.toString() << "," << c.second.toString() << endl; }
  }
*/

  // the first checks the reference and the second checks the stack
  bool hasConstraints = !constraints.isEmpty() && !constraints->isEmpty();
  ASS(!hasConstraints || !isTypeSub);
  TermList eqLHSsort = SortHelper::getEqualityArgumentSort(eqLit); 

  if(eqLHS.isVar()) { 
    //The case where eqLHS is a variable suffices because superposition 
    //is never carried out into variables. When unifying two terms
    //sort unification is guaranteed
    RobSubstitution* sub = subst->tryGetRobSubstitution();
    ASS(sub);
    TermList rwTermSort = SortHelper::getTermSort(rwTerm, rwLit);
    if(!sub->unify(eqLHSsort, eqIsResult, rwTermSort, !eqIsResult)){
      //cannot perform superposition because sorts don't unify
      return 0;
    }
  }

  if(eqLHS.isVar()) {
    if(!checkSuperpositionFromVariable(eqClause, eqLit, eqLHS)) {
      return 0;
    }
  }

  if(!checkClauseColorCompatibility(eqClause, rwClause)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned conLength = hasConstraints ? constraints->size() : 0;

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  // LRS-specific optimization:
  // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
  // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
  // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.

  unsigned numPositiveLiteralsLowerBound = Int::max(eqClause->numPositiveLiterals()-1, rwClause->numPositiveLiterals()); // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur
  //TODO update inference rule name AYB
  Inference inf(GeneratingInference2(hasConstraints ? InferenceRule::CONSTRAINED_SUPERPOSITION : InferenceRule::SUPERPOSITION, rwClause, eqClause));
  Inference::Destroyer inf_destroyer(inf);

  bool needsToFulfilWeightLimit = passiveClauseContainer && !passiveClauseContainer->fulfilsAgeLimit(0, numPositiveLiteralsLowerBound, inf) && passiveClauseContainer->weightLimited(); // 0 here denotes the current weight estimate
  if(needsToFulfilWeightLimit) {
    if(!earlyWeightLimitCheck(eqClause, eqLit, rwClause, rwLit, rwTerm, eqLHS, tgtTerm, subst, eqIsResult, passiveClauseContainer, numPositiveLiteralsLowerBound, inf)) {
      return 0;
    }
  }

  Ordering& ordering = _salg->getOrdering();

  TermList eqLHSS = subst->apply(eqLHS, eqIsResult);
  TermList tgtTermS = subst->apply(tgtTerm, eqIsResult);

  Literal* rwLitS = subst->apply(rwLit, !eqIsResult);
  TermList rwTermS = subst->apply(rwTerm, !eqIsResult);

#if VDEBUG
  if(!hasConstraints && !isTypeSub){
    ASS_EQ(rwTermS,eqLHSS);
  }
#endif

  //cout << "Check ordering on " << tgtTermS.toString() << " and " << rwTermS.toString() << endl;

  //check that we're not rewriting smaller subterm with larger
  if(Ordering::isGorGEorE(ordering.compare(tgtTermS,rwTermS))) {
    return 0;
  }

  if(rwLitS->isEquality()) {
    //check that we're not rewriting only the smaller side of an equality
    TermList arg0=*rwLitS->nthArgument(0);
    TermList arg1=*rwLitS->nthArgument(1);

    if(!arg0.containsSubterm(rwTermS)) {
      if(Ordering::isGorGEorE(ordering.getEqualityArgumentOrder(rwLitS))) {
        return 0;
      }
    } else if(!arg1.containsSubterm(rwTermS)) {
      if(Ordering::isGorGEorE(Ordering::reverse(ordering.getEqualityArgumentOrder(rwLitS)))) {
        return 0;
      }
    }
  }

  Literal* tgtLitS = EqHelper::replace(rwLitS,rwTermS,tgtTermS);

  static bool doSimS = getOptions().simulatenousSuperposition();

  //check we don't create an equational tautology (this happens during self-superposition)
  if(EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned newLength = rwLength+eqLength-1+conLength + isTypeSub;

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

      if(needsToFulfilWeightLimit) {
        weight+=currAfter->weight();
        if(!passiveClauseContainer->fulfilsWeightLimit(weight, numPositiveLiteralsLowerBound, res->inference())) {
          RSTAT_CTR_INC("superpositions skipped for weight limit while constructing other literals");
          env.statistics->discardedNonRedundantClauses++;
          goto construction_fail;
        }
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
      eqLitS = Literal::createEquality(true,eqLHSS,tgtTermS,eqLHSsort);
    }

    for(unsigned i=0;i<eqLength;i++) {
      Literal* curr=(*eqClause)[i];
      if(curr!=eqLit) {
        Literal* currAfter = subst->apply(curr, eqIsResult);

        if(EqHelper::isEqTautology(currAfter)) {
          goto construction_fail;
        }
        if(needsToFulfilWeightLimit) {
          weight+=currAfter->weight();
          if(!passiveClauseContainer->fulfilsWeightLimit(weight, numPositiveLiteralsLowerBound, res->inference())) {
            RSTAT_CTR_INC("superpositions skipped for weight limit while constructing other literals");
            env.statistics->discardedNonRedundantClauses++;
            goto construction_fail;
          }
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
      UnificationConstraint con = (*constraints)[i];

      TermList qT = subst->applyTo(con.first.first,con.first.second);
      TermList rT = subst->applyTo(con.second.first,con.second.second);

      TermList sort = SortHelper::getResultSort(rT.term());
      Literal* constraint = Literal::createEquality(false,qT,rT,sort);

      static Options::UnificationWithAbstraction uwa = env.options->unificationWithAbstraction();
      if(uwa==Options::UnificationWithAbstraction::GROUND && 
         !constraint->ground() &&
         (!UnificationWithAbstractionConfig::isInterpreted(qT) 
          && !UnificationWithAbstractionConfig::isInterpreted(rT) )) {

        // the unification was between two uninterpreted things that were not ground 
        res->destroy();
        return 0;
      }

      (*res)[next] = constraint;
      next++;   
    }
  }

  if(isTypeSub){
    TermList eqLHSsortS = subst->apply(eqLHSsort, eqIsResult);
    Literal* constraint = Literal::createEquality(false,eqLHSS,rwTermS,eqLHSsortS);
    (*res)[next] = constraint;
  }

  if(needsToFulfilWeightLimit && !passiveClauseContainer->fulfilsWeightLimit(weight, numPositiveLiteralsLowerBound, res->inference())) {
    RSTAT_CTR_INC("superpositions skipped for weight limit after the clause was built");
    env.statistics->discardedNonRedundantClauses++;
    construction_fail:
    res->destroy();
    return 0;
  }

  //TODO update AYB
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
//  cout << "result " + res->toString() << endl;
  return res;
}
