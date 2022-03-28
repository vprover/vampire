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
 * @file BinaryResolution.cpp
 * Implements class BinaryResolution.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/ColorHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BinaryResolution.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void BinaryResolution::attach(SaturationAlgorithm* salg)
{
  CALL("BinaryResolution::attach");
  ASS(!_index);

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<GeneratingLiteralIndex*> (
	  _salg->getIndexManager()->request(GENERATING_SUBST_TREE) );

  _unificationWithAbstraction = env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF;
}

void BinaryResolution::detach()
{
  CALL("BinaryResolution::detach");
  ASS(_salg);

  _index=0;
  _salg->getIndexManager()->release(GENERATING_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}


struct BinaryResolution::UnificationsFn
{
  UnificationsFn(GeneratingLiteralIndex* index,bool cU)
  : _index(index),_unificationWithAbstraction(cU) {}
  VirtualIterator<pair<Literal*, SLQueryResult> > operator()(Literal* lit)
  {
    if(lit->isEquality()) {
      //Binary resolution is not performed with equality literals
      return VirtualIterator<pair<Literal*, SLQueryResult> >::getEmpty();
    }
    if(_unificationWithAbstraction){
      return pvi( pushPairIntoRightIterator(lit, _index->getUnificationsWithConstraints(lit, true)) );
    }
    return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
  }
private:
  GeneratingLiteralIndex* _index;
  bool _unificationWithAbstraction;
};

struct BinaryResolution::ResultFn
{
  ResultFn(Clause* cl, PassiveClauseContainer* passiveClauseContainer, bool afterCheck, Ordering* ord, LiteralSelector& selector, BinaryResolution& parent)
  : _cl(cl), _passiveClauseContainer(passiveClauseContainer), _afterCheck(afterCheck), _ord(ord), _selector(selector), _parent(parent) {}
  Clause* operator()(pair<Literal*, SLQueryResult> arg)
  {
    CALL("BinaryResolution::ResultFn::operator()");

    SLQueryResult& qr = arg.second;
    Literal* resLit = arg.first;

    return BinaryResolution::generateClause(_cl, resLit, qr, _parent.getOptions(), _passiveClauseContainer, _afterCheck ? _ord : 0, &_selector);
  }
private:
  Clause* _cl;
  PassiveClauseContainer* _passiveClauseContainer;
  bool _afterCheck;
  Ordering* _ord;
  LiteralSelector& _selector;
  BinaryResolution& _parent;
};

/**
 * Ordering aftercheck is performed iff ord is not 0,
 * in which case also ls is assumed to be not 0.
 */
Clause* BinaryResolution::generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult qr, const Options& opts, PassiveClauseContainer* passiveClauseContainer, Ordering* ord, LiteralSelector* ls)
{
  CALL("BinaryResolution::generateClause");
  ASS(qr.clause->store()==Clause::ACTIVE);//Added to check that generation only uses active clauses

  if(!ColorHelper::compatible(queryCl->color(),qr.clause->color()) ) {
    env.statistics->inferencesSkippedDueToColors++;
    if(opts.showBlocked()) {
      env.beginOutput();
      env.out()<<"Blocked resolution of "<<queryCl->toString()<<" and "<<qr.clause->toString()<<endl;
      env.endOutput();
    }
    if(opts.colorUnblocking()) {
      SaturationAlgorithm* salg = SaturationAlgorithm::tryGetInstance();
      if(salg) {
        ColorHelper::tryUnblock(queryCl, salg);
        ColorHelper::tryUnblock(qr.clause, salg);
      }
    }
    return 0;
  }

  auto constraints = qr.constraints;
  bool withConstraints = !constraints.isEmpty() && !constraints->isEmpty();
  unsigned clength = queryCl->length();
  unsigned dlength = qr.clause->length();

  // LRS-specific optimization:
  // check whether we can conclude that the resulting clause will be discarded by LRS since it does not fulfil the age/weight limits (in which case we can discard the clause)
  // we already know the age here so we can immediately conclude whether the clause fulfils the age limit
  // since we have not built the clause yet we compute lower bounds on the weight of the clause after each step and recheck whether the weight-limit can still be fulfilled.
  unsigned wlb=0;//weight lower bound
  unsigned numPositiveLiteralsLowerBound = // lower bound on number of positive literals, don't know at this point whether duplicate positive literals will occur
      Int::max(queryLit->isPositive() ? queryCl->numPositiveLiterals()-1 : queryCl->numPositiveLiterals(),
              qr.literal->isPositive() ? qr.clause->numPositiveLiterals()-1 : qr.clause->numPositiveLiterals());

  Inference inf(GeneratingInference2(withConstraints?
      InferenceRule::CONSTRAINED_RESOLUTION:InferenceRule::RESOLUTION,queryCl, qr.clause));
  Inference::Destroyer inf_destroyer(inf); // will call destroy on inf when coming out of scope unless disabled

  bool needsToFulfilWeightLimit = passiveClauseContainer && !passiveClauseContainer->fulfilsAgeLimit(wlb, numPositiveLiteralsLowerBound, inf) && passiveClauseContainer->weightLimited();

  if(needsToFulfilWeightLimit) {
    for(unsigned i=0;i<clength;i++) {
      Literal* curr=(*queryCl)[i];
      if(curr!=queryLit) {
        wlb+=curr->weight();
      }
    }
    for(unsigned i=0;i<dlength;i++) {
      Literal* curr=(*qr.clause)[i];
      if(curr!=qr.literal) {
        wlb+=curr->weight();
      }
    }
    if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, inf)) {
      RSTAT_CTR_INC("binary resolutions skipped for weight limit before building clause");
      env.statistics->discardedNonRedundantClauses++;
      return 0;
    }
  }

  unsigned conlength = withConstraints ? constraints->size() : 0;
  unsigned newLength = clength+dlength-2+conlength;

  inf_destroyer.disable(); // ownership passed to the the clause below
  Clause* res = new(newLength) Clause(newLength, inf); // the inference object owned by res from now on

  Literal* queryLitAfter = 0;
  if (ord && queryCl->numSelected() > 1) {
    TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
    queryLitAfter = qr.substitution->applyToQuery(queryLit);
  }
#if VDEBUG
/*
  if(withConstraints && constraints->size() > 0){
    cout << "Other: " << qr.clause->toString() << endl;
    cout << "queryLit: " << queryLit->toString() << endl;
    cout << "resLit: " << qr.literal->toString() << endl;
    cout << "SUB:" << endl << qr.substitution->toString() << endl;
*/
/*
    cout << "SUB(deref):" << endl << qr.substitution->toString(true) << endl;
*/
  //}
#endif

  unsigned next = 0;
  if(withConstraints){
  for(unsigned i=0;i<constraints->size();i++){
      pair<pair<TermList,unsigned>,pair<TermList,unsigned>> con = (*constraints)[i]; 

#if VDEBUG
      //cout << "con pair " << con.first.toString() << " , " << con.second.toString() << endl;
#endif
  
      TermList qT = qr.substitution->applyTo(con.first.first,con.first.second);
      TermList rT = qr.substitution->applyTo(con.second.first,con.second.second);

      TermList sort = SortHelper::getResultSort(rT.term()); 

      Literal* constraint = Literal::createEquality(false,qT,rT,sort);

      static Options::UnificationWithAbstraction uwa = opts.unificationWithAbstraction();
      if(uwa==Options::UnificationWithAbstraction::GROUND &&
         !constraint->ground() &&
         (!UnificationWithAbstractionConfig::isInterpreted(qT) && 
          !UnificationWithAbstractionConfig::isInterpreted(rT))) {

        // the unification was between two uninterpreted things that were not ground 
        res->destroy();
        return 0;
      }

      (*res)[next] = constraint; 
      next++;    
  }
  }
  for(unsigned i=0;i<clength;i++) {
    Literal* curr=(*queryCl)[i];
    if(curr!=queryLit) {
      Literal* newLit=qr.substitution->applyToQuery(curr);
      if(needsToFulfilWeightLimit) {
        wlb+=newLit->weight() - curr->weight();
        if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, res->inference())) {
          RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
          env.statistics->discardedNonRedundantClauses++;
          res->destroy();
          return 0;
        }
      }
      if (queryLitAfter && i < queryCl->numSelected()) {
        TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);

        Ordering::Result o = ord->compare(newLit,queryLitAfter);

        if (o == Ordering::GREATER ||
            (ls->isPositiveForSelection(newLit)    // strict maximimality for positive literals
                && (o == Ordering::GREATER_EQ || o == Ordering::EQUAL))) { // where is GREATER_EQ ever coming from?
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          res->destroy();
          return 0;
        }
      }
      ASS(next < newLength);
      (*res)[next] = newLit;
      next++;
    }
  }

  Literal* qrLitAfter = 0;
  if (ord && qr.clause->numSelected() > 1) {
    TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
    qrLitAfter = qr.substitution->applyToResult(qr.literal);
  }

  for(unsigned i=0;i<dlength;i++) {
    Literal* curr=(*qr.clause)[i];
    if(curr!=qr.literal) {
      Literal* newLit = qr.substitution->applyToResult(curr);
      if(needsToFulfilWeightLimit) {
        wlb+=newLit->weight() - curr->weight();
        if(!passiveClauseContainer->fulfilsWeightLimit(wlb, numPositiveLiteralsLowerBound, res->inference())) {
          RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
          env.statistics->discardedNonRedundantClauses++;
          res->destroy();
          return 0;
        }
      }
      if (qrLitAfter && i < qr.clause->numSelected()) {
        TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);

        Ordering::Result o = ord->compare(newLit,qrLitAfter);

        if (o == Ordering::GREATER ||
            (ls->isPositiveForSelection(newLit)   // strict maximimality for positive literals
                && (o == Ordering::GREATER_EQ || o == Ordering::EQUAL))) { // where is GREATER_EQ ever coming from?
          env.statistics->inferencesBlockedForOrderingAftercheck++;
          res->destroy();
          return 0;
        }
      }

      (*res)[next] = newLit;
      next++;
    }
  }

  if(withConstraints){
    env.statistics->cResolution++;
  }
  else{ 
    env.statistics->resolution++;
  }

  //cout << "RESULT " << res->toString() << endl;

  return res;
}

ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  //cout << "BinaryResolution for " << premise->toString() << endl;

  PassiveClauseContainer* passiveClauseContainer = _salg->getPassiveClauseContainer();

  // generate pairs of the form (literal selected in premise, unifying object in index)
  auto it1 = getMappingIterator(premise->getSelectedLiteralIterator(),UnificationsFn(_index,_unificationWithAbstraction));
  // actually, we got one iterator per selected literal; we flatten the obtained iterator of iterators:
  auto it2 = getFlattenedIterator(it1);
  // perform binary resolution on these pairs
  auto it3 = getMappingIterator(it2,ResultFn(premise, passiveClauseContainer,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(), &_salg->getOrdering(),_salg->getLiteralSelector(),*this));
  // filter out only non-zero results
  auto it4 = getFilteredIterator(it3, NonzeroFn());
  // measure time (on the TC_RESOLUTION budget) of the overall processing
  auto it5 = getTimeCountedIterator(it4,TC_RESOLUTION);

  return pvi(it5);
}

}
