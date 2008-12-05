/**
 * @file ForwardSubsumptionResolution.cpp
 * Implements class ForwardSubsumptionResolution.
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
#include "../Kernel/MMSubstitution.hpp"

#include "../Indexing/Index.hpp"
#include "../Indexing/IndexManager.hpp"

#include "../Saturation/SaturationAlgorithm.hpp"

#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "ForwardSubsumptionResolution.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace Inferences;

void ForwardSubsumptionResolution::attach(SaturationAlgorithm* salg)
{
  CALL("SLQueryForwardSubsumption::attach");
  ForwardSimplificationEngine::attach(salg);
  _index=_salg->getIndexManager()->request(SIMPLIFYING_SUBST_TREE);
}

void ForwardSubsumptionResolution::detach()
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
  ClauseMatches() : matches(0), matchCount(0) {}

  MIList* matches;
  unsigned matchCount;
};


struct PtrHash {
  static unsigned hash(void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(ptr)>>4);
  }
};
struct PtrHash2 {
  static unsigned hash(void* ptr) {
    return static_cast<unsigned>(reinterpret_cast<size_t>(ptr)>>3);
  }
};

//typedef SkipList<ClauseMatches,ClauseMatches> CMSkipList;
typedef DHMap<Clause*,ClauseMatches, PtrHash, PtrHash2> CMMap;
typedef DHMap<Literal*, List<Literal*>*, PtrHash > MatchMap;

bool fillAlternativesArray(Clause* baseClause, MIList* matches,
	DArray<List<Literal*>*> alts)
{
  static MatchMap matchMap;
  matchMap.reset();
  MIList::Iterator miit(matches);
  while(miit.hasNext()) {
    MatchInfo minfo=miit.next();
    LiteralList** litAlts; //pointer to list of possibly matching literals of cl
    matchMap.getValuePtr(minfo.clauseLiteral, litAlts, 0);
    LiteralList::push(minfo.queryLiteral, *litAlts);
  };

  unsigned mlen=baseClause->length();
  alts.ensure(mlen);
  bool everyBaseLitHasAMatch=true;
  for(unsigned li=0;li<mlen;li++) {
    LiteralList* litAlts;
    if(matchMap.find( (*baseClause)[li], litAlts) ) {
      ASS(litAlts);
      alts[li]=litAlts;
    } else {
      alts[li]=0;
      everyBaseLitHasAMatch=false;
    }
  }
  return everyBaseLitHasAMatch;
}

bool isSubsumed(Clause* cl, CMMap* gens)
{
  static DArray<List<Literal*>*> alts(32);

  CMMap::Iterator git(*gens);
  while(git.hasNext()) {
    Clause* mcl;
    ClauseMatches clmatches;
    git.next(mcl, clmatches);

    unsigned mlen=mcl->length();
    if(mlen>clmatches.matchCount) {
      continue;
    }

    bool mclMatchFailed=!fillAlternativesArray(cl, clmatches.matches, alts);

    if(!mclMatchFailed) {
      if(!MMSubstitution::canBeMatched(cl,alts,false)) {
	mclMatchFailed=true;
      }
    }

    for(unsigned li=0;li<mlen;li++) {
      alts[li]->destroy();
    }

    if(!mclMatchFailed) {
      return true;
    }
  }
  return false;
}

Clause* generateSubsumptionResolutionClause(Clause* cl, Literal* lit)
{
  int clength = cl->length();
  int newLength = clength-1;

  Inference* inf = new Inference1(Inference::SUBSUMPTION_RESOLUTION, cl);
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

void ForwardSubsumptionResolution::perform(Clause* cl, bool& keep, ClauseIterator& toAdd)
{
  CALL("SLQueryForwardSubsumption::perform");
  toAdd=ClauseIterator::getEmpty();
  keep=true;

  unsigned clen=cl->length();
  if(clen==0) {
    return;
  }

  CMMap* gens=0;

  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getGeneralizations( (*cl)[li], false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      unsigned rlen=res.clause->length();
      if(rlen==1) {
	keep=false;
	env.statistics->forwardSubsumed++;
	goto fin;
      } else if(rlen>clen) {
	continue;
      }

      if(!gens) {
	gens=new CMMap();
      }
      ClauseMatches* cms;
      gens->getValuePtr(res.clause, cms);
      MIList::push(MatchInfo(res.literal, (*cl)[li]), cms->matches);
      cms->matchCount++;
    }
  }

  if(gens && isSubsumed(cl, gens))
  {
    keep=false;
    env.statistics->forwardSubsumed++;
    goto fin;
  }

  static DArray<List<Literal*>*> alts(32);
  for(unsigned li=0;li<clen;li++) {
    SLQueryResultIterator rit=_index->getComplementaryGeneralizations( (*cl)[li], false);
    while(rit.hasNext()) {
      SLQueryResult res=rit.next();
      Clause* mcl=res.clause;
      unsigned mlen=mcl->length();

      ClauseMatches cms;
      if(gens) {
	gens->find(mcl, cms);
      }
      if(mlen > cms.matchCount+1) {
	continue;
      }

      MIList::push(MatchInfo(res.literal, (*cl)[li]), cms.matches);
      bool mclMatchFailed=!fillAlternativesArray(mcl, cms.matches, alts);

      if(!mclMatchFailed) {
	//We know that, without the complementary literal, the call to canBeMatched
	//fails (or otherwise the clause would have been forward subsumed). So if
	//this call to canBeMatched succeeds, the complementary literal must have
	//been used.
	if(!MMSubstitution::canBeMatched(mcl,alts,true)) {
	  mclMatchFailed=true;
	}
      }
      MIList::pop(cms.matches);
      for(unsigned mli=0;mli<mlen;mli++) {
        alts[mli]->destroy();
      }
      if(!mclMatchFailed) {
	toAdd=getSingletonIterator(generateSubsumptionResolutionClause(cl,(*cl)[li]));
	keep=false;
	env.statistics->forwardSubsumed++;
	goto fin;
      }
    }
  }


fin:
  if(gens) {
    CMMap::Iterator git(*gens);
    while(git.hasNext()) {
      git.next().matches->destroy();
    }
    delete gens;
  }
}

