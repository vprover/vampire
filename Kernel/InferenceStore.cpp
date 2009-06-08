/**
 * @file InferenceStore.cpp
 * Implements class InferenceStore.
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"

#include "InferenceStore.hpp"

namespace Kernel
{

using namespace Lib;

struct InferenceStore::FullInference
{
  FullInference(unsigned premCnt) : premCnt(premCnt) {}

  void* operator new(size_t,unsigned premCnt)
  {
    size_t size=sizeof(FullInference)+premCnt*sizeof(ClauseSpec);
    size-=sizeof(ClauseSpec*);

    return ALLOC_KNOWN(size,"InferenceStore::FullInference");
  }

  unsigned premCnt;
  Inference::Rule rule;
  ClauseSpec premises[1];
};

InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl)
{
  return make_pair(cl, cl->prop());
}
InferenceStore::ClauseSpec InferenceStore::getClauseSpec(Clause* cl, BDDNode* prop)
{
  return make_pair(cl, prop);
}

void InferenceStore::recordNonPropInference(Clause* cl)
{
  CALL("InferenceStore::recordNonPropInference");

  static Stack<Clause*> prems(8);
  prems.reset();

  Inference* cinf = cl->inference();
  Inference::Iterator it = cinf->iterator();
  while (cinf->hasNext(it)) {
    Clause* prem=static_cast<Clause*>(cinf->next(it));
    ASS(prem->isClause());
    prems.push(prem);
  }

  unsigned premCnt=prems.size();
  FullInference* finf=new (premCnt) FullInference(premCnt);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->rule=cinf->rule();
  _data.insert(getClauseSpec(cl), finf);
}

void InferenceStore::recordPropReduce(Clause* cl, BDDNode* oldProp, BDDNode* newProp)
{
  recordPropAlter(cl, oldProp, newProp, Inference::PROP_REDUCE);
}

void InferenceStore::recordPropAlter(Clause* cl, BDDNode* oldProp, BDDNode* newProp,
	Inference::Rule rule)
{
  FullInference* finf=new (1) FullInference(1);
  finf->premises[0]=getClauseSpec(cl, oldProp);

  finf->rule=rule;
  _data.insert(getClauseSpec(cl, newProp), finf);
}

void InferenceStore::recordMerge(Clause* cl, BDDNode* oldClProp, Clause* addedCl, BDDNode* resultProp)
{
  FullInference* finf=new (2) FullInference(2);
  finf->premises[0]=getClauseSpec(cl, oldClProp);
  finf->premises[1]=getClauseSpec(addedCl);

  finf->rule=Inference::COMMON_NONPROP_MERGE;
  _data.insert(getClauseSpec(cl, resultProp), finf);
}

void InferenceStore::recordSplitting(Clause* master, BDDNode* oldMasterProp, BDDNode* newMasterProp,
	  unsigned premCnt, Clause** prems)
{
  FullInference* finf=new (premCnt+1) FullInference(premCnt+1);
  for(unsigned i=0;i<premCnt;i++) {
    finf->premises[i]=getClauseSpec(prems[i]);
  }
  finf->premises[premCnt]=getClauseSpec(master, oldMasterProp);

  finf->rule=Inference::SPLITTING;
  _data.insert(getClauseSpec(master, newMasterProp), finf);
}


InferenceStore* InferenceStore::instance()
{
  static InferenceStore* inst=0;
  if(!inst) {
    inst=new InferenceStore();
  }
  return inst;
}


}
