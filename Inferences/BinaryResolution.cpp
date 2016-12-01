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

#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "BinaryResolution.hpp"

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
  UnificationsFn(GeneratingLiteralIndex* index)
  : _index(index) {}
  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, SLQueryResult> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    if(lit->isEquality()) {
      //Binary resolution is not performed with equality literals
      return OWN_RETURN_TYPE::getEmpty();
    }
    return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
  }
private:
  GeneratingLiteralIndex* _index;
};

struct BinaryResolution::ResultFn
{
  ResultFn(Clause* cl, Limits* limits, bool afterCheck, Ordering* ord, LiteralSelector& selector, BinaryResolution& parent)
  : _cl(cl), _limits(limits), _afterCheck(afterCheck), _ord(ord), _selector(selector), _parent(parent) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, SLQueryResult> arg)
  {
    CALL("BinaryResolution::ResultFn::operator()");

    SLQueryResult& qr = arg.second;
    Literal* resLit = arg.first;

    return BinaryResolution::generateClause(_cl, resLit, qr, _parent.getOptions(), _limits, _afterCheck ? _ord : 0, &_selector);
  }
private:
  Clause* _cl;
  Limits* _limits;
  bool _afterCheck;
  Ordering* _ord;
  LiteralSelector& _selector;
  BinaryResolution& _parent;
};

/**
 * Ordering aftercheck is performed iff ord is not 0,
 * in which case also ls is assumed to be not 0.
 */
Clause* BinaryResolution::generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult qr, const Options& opts, Limits* limits, Ordering* ord, LiteralSelector* ls)
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

  unsigned clength = queryCl->length();
  unsigned dlength = qr.clause->length();
  unsigned newAge=Int::max(queryCl->age(),qr.clause->age())+1;
  bool shouldLimitWeight=limits && limits->ageLimited() && newAge > limits->ageLimit()
	&& limits->weightLimited();
  unsigned weightLimit;
  if(shouldLimitWeight) {
    bool isNonGoal=queryCl->inputType()==0 && qr.clause->inputType()==0;
    if(isNonGoal) {
      weightLimit=limits->nonGoalWeightLimit();
    } else {
      weightLimit=limits->weightLimit();
    }
  }


  unsigned wlb=0;//weight lower bound
  if(shouldLimitWeight) {
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
    if(wlb > weightLimit) {
      RSTAT_CTR_INC("binary resolutions skipped for weight limit before building clause");
      env.statistics->discardedNonRedundantClauses++;
      return 0;
    }
  }

  unsigned newLength = clength+dlength-2;

  Inference* inf = new Inference2(Inference::RESOLUTION, queryCl, qr.clause);
  Unit::InputType inpType = (Unit::InputType)
  	Int::max(queryCl->inputType(), qr.clause->inputType());

  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  Literal* queryLitAfter = 0;
  if (ord && queryCl->numSelected() > 1) {
    TimeCounter tc(TC_LITERAL_ORDER_AFTERCHECK);
    queryLitAfter = qr.substitution->applyToQuery(queryLit);
  }

  unsigned next = 0;
  for(unsigned i=0;i<clength;i++) {
    Literal* curr=(*queryCl)[i];
    if(curr!=queryLit) {
      Literal* newLit=qr.substitution->applyToQuery(curr);
      if(shouldLimitWeight) {
        wlb+=newLit->weight() - curr->weight();
        if(wlb > weightLimit) {
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
      if(shouldLimitWeight) {
        wlb+=newLit->weight() - curr->weight();
        if(wlb > weightLimit) {
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

  res->setAge(newAge);
  env.statistics->resolution++;

  return res;
}

ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  cout << "BinaryResolution for " << premise->toString() << endl;

  Limits* limits = _salg->getLimits();

  // generate pairs of the form (literal selected in premise, unifying object in index)
  auto it1 = getMappingIterator(premise->getSelectedLiteralIterator(),UnificationsFn(_index));
  // actually, we got one iterator per selected literal; we flatten the obtained iterator of iterators:
  auto it2 = getFlattenedIterator(it1);
  // perform binary resolution on these pairs
  auto it3 = getMappingIterator(it2,ResultFn(premise, limits,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(), &_salg->getOrdering(),_salg->getLiteralSelector(),*this));
  // filter out only non-zero results
  auto it4 = getFilteredIterator(it3, NonzeroFn());
  // measure time (on the TC_RESOLUTION budget) of the overall processing
  auto it5 = getTimeCountedIterator(it4,TC_RESOLUTION);

  return pvi(it5);
}

}
