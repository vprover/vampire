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
  ResultFn(Clause* cl, Limits* limits, BinaryResolution& parent)
  : _cl(cl), _limits(limits), _parent(parent) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, SLQueryResult> arg)
  {
    CALL("BinaryResolution::ResultFn::operator()");

    SLQueryResult& qr = arg.second;
    Literal* resLit = arg.first;

    return BinaryResolution::generateClause(_cl, resLit, qr, _parent.getOptions(), _limits);
  }
private:
  Clause* _cl;
  Limits* _limits;
  BinaryResolution& _parent;
};

Clause* BinaryResolution::generateClause(Clause* queryCl, Literal* queryLit, SLQueryResult qr, const Options& opts, Limits* limits)
{
  CALL("BinaryResolution::generateClause");
  ASS(qr.clause->store()==Clause::ACTIVE);//Added to check that generation only uses active clauses

  if(!ColorHelper::compatible(queryCl->color(),qr.clause->color()) ) {
    env -> statistics->inferencesSkippedDueToColors++;
    if(opts.showBlocked()) {
      env -> beginOutput();
      env -> out()<<"Blocked resolution of "<<queryCl->toString()<<" and "<<qr.clause->toString()<<endl;
      env -> endOutput();
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
  int newAge=Int::max(queryCl->age(),qr.clause->age())+1;
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
      env -> statistics->discardedNonRedundantClauses++;
      return 0;
    }
  }

  unsigned newLength = clength+dlength-2;

  Inference* inf = new Inference2(Inference::RESOLUTION, queryCl, qr.clause);
  Unit::InputType inpType = (Unit::InputType)
  	Int::max(queryCl->inputType(), qr.clause->inputType());

  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  unsigned next = 0;
  for(unsigned i=0;i<clength;i++) {
    Literal* curr=(*queryCl)[i];
    if(curr!=queryLit) {
      Literal* newLit=qr.substitution->applyToQuery(curr);
      if(shouldLimitWeight) {
	wlb+=newLit->weight() - curr->weight();
	if(wlb > weightLimit) {
	  RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
	  env -> statistics->discardedNonRedundantClauses++;
	  res->destroy();
	  return 0;
	}
      }
      (*res)[next] = newLit;
      next++;
    }
  }
  for(unsigned i=0;i<dlength;i++) {
    Literal* curr=(*qr.clause)[i];
    if(curr!=qr.literal) {
      Literal* newLit = qr.substitution->applyToResult(curr);
      if(shouldLimitWeight) {
	wlb+=newLit->weight() - curr->weight();
	if(wlb > weightLimit) {
	  RSTAT_CTR_INC("binary resolutions skipped for weight limit while building clause");
	  env -> statistics->discardedNonRedundantClauses++;
	  res->destroy();
	  return 0;
	}
      }
      (*res)[next] = newLit;
      next++;
    }
  }

  res->setAge(newAge);
  env -> statistics->resolution++;

  return res;
}

ClauseIterator BinaryResolution::generateClauses(Clause* premise)
{
  CALL("BinaryResolution::generateClauses");

  Limits* limits=_salg->getLimits();
  return pvi( getTimeCountedIterator(
    getFilteredIterator(
      getMappingIterator(
	  getFlattenedIterator(
		  getMappingIterator(
			  premise->getSelectedLiteralIterator(),
			  UnificationsFn(_index))),
	  ResultFn(premise, limits, *this)),
      NonzeroFn()
    ), TC_RESOLUTION ) );
}

}
