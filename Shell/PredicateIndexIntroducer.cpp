/**
 * @file PredicateIndexIntroducer.cpp
 * Implements class PredicateIndexIntroducer.
 */

#include <algorithm>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Hash.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Options.hpp"

#include "PredicateIndexIntroducer.hpp"

namespace Shell
{

PredicateIndexIntroducer::PredicateIndexIntroducer()
 : ScanAndApplyLiteralTransformer(Inference::DEFINITION_FOLDING)
{
  CALL("PredicateIndexIntroducer::PredicateIndexIntroducer");

  _assumeSSDistinctGroup = true;
  _ssDistinctGroupID = 0xFFFFFFFF;
}

void PredicateIndexIntroducer::scan(UnitList* units)
{
  CALL("PredicateIndexIntroducer::scan");

  static LiteralStack atoms;

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    atoms.reset();
    u->collectAtoms(atoms);

    while(atoms.isNonEmpty()) {
      scan(atoms.pop());
    }
  }

  ArgOccInfoMap::Iterator aiit(_predArgOccInfos);
  while(aiit.hasNext()) {
    ArgId ai;
    ArgOccInfo inf;
    aiit.next(ai, inf);
    if(!inf._eligible) {
      continue;
    }
    Stack<unsigned>* idxArgs;
    _indexedPredArgs.getValuePtr(ai.first, idxArgs);
    idxArgs->push(ai.second);
  }

  IdxPredArgsMap::Iterator ipit(_indexedPredArgs);
  while(ipit.hasNext()) {
    unsigned pred = ipit.nextKey();
    Stack<unsigned>& args = _indexedPredArgs.get(pred);
    std::sort(args.begin(), args.end());
    if (env->options->showPreprocessing()) {
      env->beginOutput();
      env->out() << "[PP] elim pred: "<<env->signature->predicateName(pred) << std::endl;
      env->endOutput();
    }
  }
  RSTAT_CTR_INC_MANY("predicates removed by indexing", _indexedPredArgs.size());
}

PredicateIndexIntroducer::DistGrpSet* PredicateIndexIntroducer::getDistGrps(TermList trm)
{
  CALL("PredicateIndexIntroducer::getDistGrps");

  if(!trm.isTerm() || trm.term()->arity()!=0) {
    return DistGrpSet::getEmpty();
  }
  unsigned func = trm.term()->functor();
  const List<unsigned>* signDistGrps = env -> signature->getFunction(func)->distinctGroups();

  static Stack<unsigned> distGrps;

  distGrps.reset();
  distGrps.loadFromIterator(List<unsigned>::Iterator(signDistGrps));

  if(_assumeSSDistinctGroup) {
    vstring name = trm.term()->functionName();
    bool ssDistinct = name.substr(0,2)=="$$";

    vstring protectedPrefix = env -> options->protectedPrefix();
    if(!ssDistinct && protectedPrefix.size()!=0) {
      if(name.substr(0, protectedPrefix.size())==protectedPrefix) {
	ssDistinct = true;
      }
    }

    if(ssDistinct) {
      distGrps.push(_ssDistinctGroupID);
    }

  }

  return DistGrpSet::getFromArray(distGrps.begin(), distGrps.size());
}

void PredicateIndexIntroducer::ArgOccInfo::scanArg(PredicateIndexIntroducer& parent, TermList trm)
{
  CALL("PredicateIndexIntroducer::ArgOccInfo::scanArg");

  bool wasNew = _new;
  if(_new) {
    _new = false;
    _eligible = true;
  }
  else if(!_eligible) {
    return;
  }
  if(!trm.isTerm() || trm.term()->arity()!=0) {
    _eligible = false;
    return;
  }

  if(wasNew) {
    _onlyOcc = trm.term();
    _distGrps = parent.getDistGrps(trm);
    return;
  }
  else if(_onlyOcc) {
    if(_onlyOcc==trm.term()) {
      return;
    }
    _onlyOcc = 0;
    if(_distGrps->isEmpty()) {
      _eligible = false;
      return;
    }
  }
  ASS(!_onlyOcc);
  ASS(_distGrps);
  ASS(!_distGrps->isEmpty());
  DistGrpSet* trmDistGrps = parent.getDistGrps(trm);
  _distGrps = _distGrps->getIntersection(trmDistGrps);

  if(_distGrps->isEmpty()) {
    _eligible = false;
  }
}

void PredicateIndexIntroducer::scan(Literal* lit)
{
  CALL("PredicateIndexIntroducer::scan(Literal*)");

  if(env -> signature->getPredicate(lit->functor())->protectedSymbol()) {
    return;
  }

  if(!_seen.insert(lit)) {
    return;
  }

  unsigned func = lit->functor();
  unsigned arity = lit->arity();

  for(unsigned i=0; i<arity; ++i) {
    TermList arg = *lit->nthArgument(i);
    ArgId ai = ArgId(func, i);
    ArgOccInfo* pInfo;
    _predArgOccInfos.getValuePtr(ai, pInfo);
    pInfo->scanArg(*this, arg);
  }
}

unsigned PredicateIndexIntroducer::getIndexedPred(Literal* lit)
{
  CALL("PredicateIndexIntroducer::getIndexedPred");

  unsigned pred = lit->functor();
  ASS(_indexedPredArgs.find(pred));

  Stack<unsigned>& indexedArgs = _indexedPredArgs.get(pred);

  //collect arguments which we use for indexing
  static TermStack idxTerms;
  idxTerms.reset();
  Stack<unsigned>::BottomFirstIterator iaIdxIt(indexedArgs); //indexed argument index iterator
  while(iaIdxIt.hasNext()) {
    unsigned iaIdx = iaIdxIt.next();
    idxTerms.push(*lit->nthArgument(iaIdx));
  }

  IdxPredKey key(pred,idxTerms);

  unsigned* pRes;
  if(!_idxPreds.getValuePtr(key, pRes)) {
    return *pRes;
  }

  unsigned remainingArity = lit->arity() - indexedArgs.size();


  vstring suffix = lit->predicateName();


  //build a nice suffix for the newly introduced predicate
  TermStack::BottomFirstIterator itit(idxTerms);
  while(itit.hasNext()) {
    TermList t = itit.next();
    ASS(t.isTerm());
    ASS(t.term()->arity()==0);

    suffix += "_" + t.term()->functionName();
  }
  suffix = StringUtils::sanitizeSuffix(suffix);


  //collect sorts of the non-indexed arguments
  static Stack<unsigned> argSorts;
  argSorts.reset();

  ASS(isSorted(Stack<unsigned>::BottomFirstIterator(indexedArgs)));
  Stack<unsigned>::BottomFirstIterator iaIdxIt2(indexedArgs);
  ALWAYS(iaIdxIt2.hasNext());
  unsigned nextIndexedIdx = iaIdxIt2.next();
  unsigned arity = lit->arity();

  for(unsigned i=0; i<arity; ++i) {
    if(i==nextIndexedIdx) {
      //make sure we'll spot the next indexed argument index (the "index" word is a bit too much overloaded...)
      if(iaIdxIt2.hasNext()) {
	nextIndexedIdx = iaIdxIt2.next();
      }
      else {
	nextIndexedIdx=0; //we won't have i==0 in the next iterations
      }
      continue;
    }
    argSorts.push(SortHelper::getArgSort(lit, i));
  }



  *pRes = env -> signature->addFreshPredicate(remainingArity, "sP", suffix.c_str());
  ASS_EQ(remainingArity, argSorts.size());
  BaseType* predType = BaseType::makeType(remainingArity, argSorts.begin(), Sorts::SRT_BOOL);
  env -> signature->getPredicate(*pRes)->setType(predType);

  RSTAT_CTR_INC("introduced index predicates");
  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] introduced index predicate: "<<env->signature->predicateName(*pRes)
            << " of type "<<predType->toString() << std::endl;
    env->endOutput();
  }  

  return *pRes;
}

Literal* PredicateIndexIntroducer::apply(Literal* lit, UnitStack& premAcc)
{
  CALL("PredicateIndexIntroducer::apply");

  unsigned pred = lit->functor();
  if(!_indexedPredArgs.find(pred)) {
    return lit;
  }

  unsigned idxPred = getIndexedPred(lit);

  Stack<unsigned>& indexedArgs = _indexedPredArgs.get(pred);

  //collect arguments that remained after indexing
  static TermStack args;
  args.reset();

  Stack<unsigned>::BottomFirstIterator iaIdxIt(indexedArgs); //indexed argument index iterator
  ALWAYS(iaIdxIt.hasNext());
  unsigned nextIndexedIdx = iaIdxIt.next();
  unsigned arity = lit->arity();

  for(unsigned i=0; i<arity; ++i) {
    if(i==nextIndexedIdx) {
      if(iaIdxIt.hasNext()) {
	nextIndexedIdx = iaIdxIt.next();
      }
      else {
	nextIndexedIdx=0; //we won't have i==0 in the next iterations
      }
      continue;
    }
    args.push(*lit->nthArgument(i));
  }

  ASS_EQ(args.size()+indexedArgs.size(), arity);

  //TODO: add transformation premise into premAcc
  RSTAT_CTR_INC("introduced index predicate occurrences");
  Literal* res = Literal::create(idxPred, args.size(), lit->polarity(), false, args.begin());

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] rewrite: "<<(*lit)<<" --> "<<(*res) << std::endl;
    env->endOutput();
  }

  return res;
}


void PredicateIndexIntroducer::updateModifiedProblem(Problem& prb)
{
  CALL("PredicateIndexIntroducer::updateModifiedProblem");

  prb.invalidateProperty();

  //TODO: registed eliminated predicates by call to prb.addEliminatedPredicate()
}

}
