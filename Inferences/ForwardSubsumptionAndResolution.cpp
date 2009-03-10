/**
 * @file ForwardSubsumptionAndResolution.cpp
 * Implements class ForwardSubsumptionAndResolution.
 */


#include "../Lib/VirtualIterator.hpp"
#include "../Lib/BacktrackData.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Metaiterators.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/Inference.hpp"
#include "../Kernel/MLMatcher.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/LiteralIndex.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "ForwardSubsumptionAndResolution.hpp"

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
  _index=static_cast<SimplifyingLiteralIndex*>(
	  _salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE) );
}

void ForwardSubsumptionAndResolution::detach()
{
  CALL("SLQueryForwardSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(SIMPLIFYING_SUBST_TREE);
  ForwardSimplificationEngine::detach();
}


struct MatchInfo {
  MatchInfo() {}
  MatchInfo(Literal* cLit, Literal* qLit)
  : clauseLiteral(cLit), queryLiteral(qLit) {}
  Literal* clauseLiteral;
  Literal* queryLiteral;

};

typedef List<MatchInfo> MIList;

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
    unsigned bpos=_cl->getLiteralPosition(baseLit);
    if(!_matches[bpos]) {
      _zeroCnt--;
    }
    LiteralList::push(instLit,_matches[bpos]);
  }
  bool anyNonMatched() { return _zeroCnt; }

  Clause* _cl;
  unsigned _zeroCnt;
  LiteralList** _matches;
};


typedef DHMap<Clause*,ClauseMatches*, PtrIdentityHash> CMMap;


bool isSubsumed(Clause* cl, CMMap* gens)
{
  CALL("isSubsumed");

  CMMap::Iterator git(*gens);
  while(git.hasNext()) {
    Clause* mcl;
    ClauseMatches* clmatches;
    git.next(mcl, clmatches);

    if(clmatches->anyNonMatched()) {
      continue;
    }

    if(MLMatcher::canBeMatched(mcl,clmatches->_matches)) {
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
  Unit::InputType inpType = cl->inputType();

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

  res->setAge(cl->age()+1);
  env.statistics->forwardSubsumptionResolution++;

  return res;
}

void ForwardSubsumptionAndResolution::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("ForwardSubsumptionResolution::perform");
  toAdd=ClauseIterator::getEmpty();
  keep=true;

  unsigned clen=cl->length();
  if(clen==0) {
    return;
  }

  CMMap* gens=0;

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getGeneralizations( (*cl)[li], false, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      unsigned rlen=res.clause->length();
      if(rlen==1) {
	keep=false;
	env.statistics->forwardSubsumed++;
	goto fin;
      }

      if(!gens) {
	gens=new CMMap();
      }
      ClauseMatches** pcms;
      if(gens->getValuePtr(res.clause, pcms)) {
	*pcms=new ClauseMatches(res.clause);
      }
      (*pcms)->addMatch(res.literal, (*cl)[li]);
    }
  }

  if(gens && isSubsumed(cl, gens))
  {
    keep=false;
    env.statistics->forwardSubsumed++;
    goto fin;
  }

  static DArray<LiteralList*> alts(32);
  for(unsigned li=0;li<clen;li++) {
    Literal* resLit=(*cl)[li];	//resolved literal
    Set<Clause*> matchedClauses;
    SLQueryResultIterator rit=_index->getGeneralizations( resLit, true, false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      Clause* mcl=res.clause;
      unsigned mlen=mcl->length();

      bool success;
      if(mlen==1) {
	success=true;
      } else {
	if(matchedClauses.contains(mcl)) {
	  continue;
	}
	matchedClauses.insert(mcl);

	ClauseMatches* cms=0;
	if(gens) {
	  gens->find(mcl, cms);
	}
	if(cms) {
	  //TODO: wrong! must remove the resLit from matching!
	  success=MLMatcher::checkForSubsumptionResolution(mcl,cms->_matches,resLit);
	} else {
	  success=false;
	}
      }

      if(success) {
	toAdd=pvi( getSingletonIterator(generateSubsumptionResolutionClause(cl,resLit,mcl)) );
	keep=false;
	goto fin;
      }
    }
  }


fin:
  if(gens) {
    CMMap::Iterator git(*gens);
    while(git.hasNext()) {
      delete git.next();
    }
    delete gens;
  }
}

}
