/**
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution.
 */


#include "../Lib/VirtualIterator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Metaiterators.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/Matcher.hpp"
#include "../Kernel/MLMatcher.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/LiteralMiniIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "ForwardSubsumptionAndResolution.hpp"

extern bool reporting;

namespace Inferences
{
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ForwardSubsumptionAndResolution::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _unitIndex=static_cast<UnitClauseSimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE) );
  _fwIndex=static_cast<FwSubsSimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(FW_SUBSUMPTION_SUBST_TREE) );
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _unitIndex=0;
  _fwIndex=0;
  _salg->getIndexManager()->release(SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE);
  _salg->getIndexManager()->release(FW_SUBSUMPTION_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


struct ClauseMatches {
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  ClauseMatches(const ClauseMatches&);
  ClauseMatches& operator=(const ClauseMatches&);
public:
  ClauseMatches(Clause* cl) : _cl(cl), _zeroCnt(cl->length())
  {
    unsigned clen=_cl->length();
    _matches=static_cast<LiteralList**>(ALLOC_KNOWN(clen*sizeof(void*), "Inferences::ClauseMatches"));
    for(unsigned i=0;i<clen;i++) {
      _matches[i]=0;
    }
  }
  ~ClauseMatches()
  {
    unsigned clen=_cl->length();
    for(unsigned i=0;i<clen;i++) {
      _matches[i]->destroy();
    }
    DEALLOC_KNOWN(_matches, clen*sizeof(void*), "Inferences::ClauseMatches");
  }

  void addMatch(Literal* baseLit, Literal* instLit)
  {
    addMatch(_cl->getLiteralPosition(baseLit), instLit);
  }
  void addMatch(unsigned bpos, Literal* instLit)
  {
    if(!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit,_matches[bpos]);
  }
  void fillInMatches(LiteralMiniIndex* miniIndex)
  {
    unsigned blen=_cl->length();

    for(unsigned bi=0;bi<blen;bi++) {
      LiteralMiniIndex::InstanceIterator instIt(*miniIndex, (*_cl)[bi], false);
      while(instIt.hasNext()) {
	addMatch(bi, instIt.next());
      }
    }
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause* _cl;
  unsigned _zeroCnt;
  LiteralList** _matches;

  class ZeroMatchLiteralIterator
  {
  public:
    ZeroMatchLiteralIterator(ClauseMatches* cm)
    : _lits(cm->_cl->literals()), _mlists(cm->_matches), _remaining(cm->_cl->length())
    {
      if(!cm->_zeroCnt) {
	_remaining=0;
      }
    }
    bool hasNext()
    {
      while(_remaining>0 && *_mlists) {
	_lits++; _mlists++; _remaining--;
      }
      return _remaining;
    }
    Literal* next()
    {
      _remaining--;
      _mlists++;
      return *(_lits++);
    }
  private:
    Literal** _lits;
    LiteralList** _mlists;
    unsigned _remaining;
  };
};


typedef Stack<ClauseMatches*> CMStack;

bool isSubsumed(Clause* cl, CMStack& cmStore)
{
  CALL("isSubsumed");

  CMStack::Iterator csit(cmStore);
  while(csit.hasNext()) {
    ClauseMatches* clmatches;
    clmatches=csit.next();
    Clause* mcl=clmatches->_cl;

    if(clmatches->anyNonMatched()) {
      continue;
    }

    if(MLMatcher::canBeMatched(mcl,cl,clmatches->_matches,0)) {
      return true;
    }
  }
  return false;
}

Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit, Clause* baseClause)
{
  CALL("generateSubsumptionResolutionClause");
  int clength = cl->length();
  int newLength = clength-1;

  Inference* inf = new Inference2(Inference::SUBSUMPTION_RESOLUTION, cl, baseClause);
  Unit::InputType inpType = (Unit::InputType)
  	max(cl->inputType(), baseClause->inputType());

  Clause* res = new(newLength) Clause(newLength, inpType, inf);

  int next = 0;
  bool found=false;
  for(int i=0;i<clength;i++) {
    Literal* curr=(*cl)[i];
    //As we will apply subsumption resolution after duplicate literal
    //deletion, the same literal should never occur twice.
    ASS(curr!=lit || !found);
    if(curr!=lit || found) {
	(*res)[next++] = curr;
    } else {
      found=true;
    }
  }

  res->setAge(max(cl->age(), baseClause->age())+1);
  env.statistics->forwardSubsumptionResolution++;

  return res;
}

bool checkForSubsumptionResolution(Clause* cl, ClauseMatches* cms, Literal* resLit)
{
  Clause* mcl=cms->_cl;
  unsigned mclen=mcl->length();

  ClauseMatches::ZeroMatchLiteralIterator zmli(cms);
  if(zmli.hasNext()) {
    while(zmli.hasNext()) {
      Literal* bl=zmli.next();
      if( !resLit->couldBeInstanceOf(bl, true) ) {
	return false;
      }
    }
  } else {
    bool anyResolvable=false;
    for(unsigned i=0;i<mclen;i++) {
      if(resLit->couldBeInstanceOf((*mcl)[i], true)) {
	anyResolvable=true;
	break;
      }
    }
    if(!anyResolvable) {
      return false;
    }
  }

  return MLMatcher::canBeMatched(mcl,cl,cms->_matches,resLit);
}

void ForwardSubsumptionAndResolution::perform(Clause* cl, bool& keep, ClauseIterator& toAdd,
	ClauseIterator& premises)
{
  CALL("ForwardSubsumptionResolution::perform");

  toAdd=ClauseIterator::getEmpty();
  premises=ClauseIterator::getEmpty();
  keep=true;
  Clause* resolutionClause=0;

//  if(cl->number()==180) {
//    reporting=true;
//  }

  unsigned clen=cl->length();
  if(clen==0) {
    return;
  }


  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_unitIndex->getGeneralizations( (*cl)[li], false, false);
    if(rit.hasNext()) {
      keep=false;
      premises=pvi( getSingletonIterator(rit.next().clause) );
      env.statistics->forwardSubsumed++;
      return;
    }
  }

  LiteralMiniIndex miniIndex(cl);
  Clause::requestAux();

  static CMStack cmStore(64);
  ASS(cmStore.isEmpty());

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_fwIndex->getGeneralizations( (*cl)[li], false, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      Clause* mcl=res.clause;
      if(mcl->hasAux()) {
	//we've already checked this clause
	continue;
      }
      unsigned mlen=mcl->length();
      ASS_G(mlen,1);

      ClauseMatches* cms=new ClauseMatches(mcl);
      mcl->setAux(cms);
      cmStore.push(cms);
//      cms->addMatch(res.literal, (*cl)[li]);
//      cms->fillInMatches(&miniIndex, res.literal, (*cl)[li]);
      cms->fillInMatches(&miniIndex);

      if(cms->anyNonMatched()) {
        continue;
      }

      if(MLMatcher::canBeMatched(mcl,cl,cms->_matches,0)) {
	keep=false;
	premises=pvi( getSingletonIterator(mcl) );
	env.statistics->forwardSubsumed++;
	goto fin;
      }
    }
  }


  for(unsigned li=0;li<clen;li++) {
    Literal* resLit=(*cl)[li];
    SLQueryResultIterator rit=_unitIndex->getGeneralizations( resLit, true, false);
    if(rit.hasNext()) {
      Clause* mcl=rit.next().clause;
      resolutionClause=generateSubsumptionResolutionClause(cl,resLit,mcl);
      premises=pvi( getSingletonIterator(mcl) );
      goto fin;
    }
  }

  {
    CMStack::Iterator csit(cmStore);
    while(csit.hasNext()) {
      ClauseMatches* cms=csit.next();
      for(unsigned li=0;li<clen;li++) {
	Literal* resLit=(*cl)[li];
	if(checkForSubsumptionResolution(cl, cms, resLit)) {
	  resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
	  premises=pvi( getSingletonIterator(cms->_cl) );
	  goto fin;
	}
      }
    }
  }

  for(unsigned li=0;li<clen;li++) {
    Literal* resLit=(*cl)[li];	//resolved literal
    Set<Clause*> matchedClauses;
    SLQueryResultIterator rit=_fwIndex->getGeneralizations( resLit, true, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      Clause* mcl=res.clause;

      if(mcl->hasAux()) {
	//we have already examined this clause
	continue;
      }

      ClauseMatches* cms=new ClauseMatches(mcl);
      res.clause->setAux(cms);
      cmStore.push(cms);
      cms->fillInMatches(&miniIndex);

      if(checkForSubsumptionResolution(cl, cms, resLit)) {
	resolutionClause=generateSubsumptionResolutionClause(cl,resLit,cms->_cl);
	premises=pvi( getSingletonIterator(cms->_cl) );
	goto fin;
      }
    }
  }


fin:
  Clause::releaseAux();
  while(cmStore.isNonEmpty()) {
    delete cmStore.pop();
  }

  if(resolutionClause) {
    keep=false;
    toAdd=pvi( getSingletonIterator(resolutionClause) );
  }

}

}
