/**
 * @file SAT/Preprocess.cpp
 * Implements class Preprocess.
 */

//TODO: Rename the file!
//It is currently not included in the MSVC project, as it has the same name as
//Shell/Preprocess.cpp and the MSVC2008 linker is not able to handle this.

#include <algorithm>
#include <iostream>
#include <fstream>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Random.hpp"
#include "Lib/Int.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Stack.hpp"

#include "SATClause.hpp"
//#include "SATInference.hpp"

#include "Preprocess.hpp"

namespace SAT
{

using namespace Lib;

SATClauseIterator Preprocess::filterPureLiterals(unsigned varCnt, SATClauseIterator clauses)
{
  CALL("Preprocess::filterPureLiterals");

  static Stack<unsigned> pureVars(64);
  static DArray<int> positiveOccurences(128);
  static DArray<int> negativeOccurences(128);
  static DArray<SATClauseList*> occurences(128);
  positiveOccurences.init(varCnt, 0);
  negativeOccurences.init(varCnt, 0);
  occurences.init(varCnt, 0);

  SATClauseList* res=0;

  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();

    cl->setKept(true);
    SATClauseList::push(cl, res);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral lit=(*cl)[i];
      unsigned var=lit.var();
      SATClauseList::push(cl,occurences[var]);
      if(lit.isPositive()) {
	positiveOccurences[var]++;
      } else {
	negativeOccurences[var]++;
      }
    }
  }

  for(unsigned i=0;i<varCnt;i++) {
    if( ((positiveOccurences[i]!=0)^(negativeOccurences[i]!=0)) && occurences[i] ) {
      pureVars.push(i);
    }
  }

  while(pureVars.isNonEmpty()) {
    unsigned var=pureVars.pop();

    while(occurences[var]) {
      SATClause* cl=SATClauseList::pop(occurences[var]);
      if(!cl->kept()) {
	continue;
      }
      cl->setKept(false);

      unsigned clen=cl->length();
      for(unsigned i=0;i<clen;i++) {
	SATLiteral lit=(*cl)[i];
	unsigned lvar=lit.var();
	if(lit.isPositive()) {
	  positiveOccurences[lvar]--;
	  if( positiveOccurences[lvar]==0 && negativeOccurences[lvar]!=0 && occurences[lvar] ) {
	    pureVars.push(lvar);
	  }
	} else {
	  negativeOccurences[lvar]--;
	  if( positiveOccurences[lvar]!=0 && negativeOccurences[lvar]==0 && occurences[lvar] ) {
	    pureVars.push(lvar);
	  }
	}
      }
    }

  }

  for(unsigned i=0;i<varCnt;i++) {
    occurences[i]->destroy();
  }

  SATClauseList::DelIterator rit(res);
  while(rit.hasNext()) {
    SATClause* cl=rit.next();
    if(!cl->kept()) {
      rit.del();
    }
  }

  return pvi( SATClauseList::DestructiveIterator(res) );
}


void Preprocess::propagateUnits(SATClauseIterator clauses,
	SATClauseIterator& resUnits, SATClauseIterator& resNonUnits)
{
  CALL("Preprocess::propagateUnits");

  static DHMap<unsigned, bool, IdentityHash> unitBindings;
  static Stack<unsigned> removedLitIndexes(64);

  unitBindings.reset();
  SATClauseList* res=0;
  SATClauseList* units=0;

  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();
    if(cl->length()==1) {
      SATLiteral unit=(*cl)[0];
      bool oldPolarity;
      if(unitBindings.find(unit.var(), oldPolarity)) {
	if(oldPolarity!=unit.isPositive()) {
	  res->destroy();
	  units->destroy();
	  resUnits=SATClauseIterator::getEmpty();
	  resNonUnits=pvi( getSingletonIterator(new(0) SATClause(0, true)) );
	  return;
	}
      } else {
	SATClauseList::push(cl, units);
	unitBindings.insert(unit.var(), unit.isPositive());
      }
    } else {
      SATClauseList::push(cl, res);
    }
  }

propagation_start:
  bool newUnit=false;

  SATClauseList::DelIterator rit(res);
  while(rit.hasNext()) {
    SATClause* cl=rit.next();
    unsigned clen=cl->length();
    bool del=false;
    removedLitIndexes.reset();
    SATLiteral kept;
    for(unsigned i=0;i<clen;i++) {
      SATLiteral lit=(*cl)[i];
      bool posUnit;
      if(!unitBindings.find(lit.var(), posUnit)) {
	kept=lit;
	continue;
      }
      if(posUnit==lit.isPositive()) {
	del=true;
	break;
      }
      removedLitIndexes.push(i);
    }
    if(del) {
      rit.del();
      cl->destroy();
      continue;
    }
    if(removedLitIndexes.isEmpty()) {
      continue;
    }
    unsigned newLen=clen-removedLitIndexes.length();

    if(newLen==1) {
      SATClause* unit=new(1) SATClause(1, true);
      (*unit)[0]=kept;
      SATClauseList::push(unit, units);

      unitBindings.insert(kept.var(), kept.isPositive());
      rit.del();
      cl->destroy();
      newUnit=true;
      continue;
    }

    SATClause* cl2=new(newLen) SATClause(newLen, true);


    removedLitIndexes.push(0xFFFFFFFF);//a stopper
    unsigned nextRLI=0;
    unsigned next=0;
    for(unsigned i=0;i<clen;i++) {
      if(removedLitIndexes[nextRLI]==i) {
	nextRLI++;
      } else {
	(*cl2)[next++]=(*cl)[i];
      }
    }
    ASS_EQ(next, newLen);

    rit.replace(cl2);
    cl->destroy();
  }

  if(newUnit) {
    goto propagation_start;
  }

  resUnits=pvi( SATClauseList::DestructiveIterator(units) );
  resNonUnits=pvi( SATClauseList::DestructiveIterator(res) );
  return;
}

void Preprocess::createVarProfile(unsigned var, DArray<unsigned>& profile, DArray<SATClauseList*>& clsByVar,
    Set<unsigned>& fixed)
{
  CALL("Preprocess::createVarProfile");

  profile.ensure(0);
  SATClauseList::Iterator vcit(clsByVar[var]);
  while(vcit.hasNext()) {
    SATClause* cl=vcit.next();
    unsigned clen=cl->length();
    unsigned unassignedCnt=0;
    for(unsigned li=0;li<clen;li++) {
      unsigned lvar=(*cl)[li].var();
      if(lvar!=var && !fixed.contains(lvar)) {
	unassignedCnt++;
      }
    }

    if(unassignedCnt>=profile.size()) {
      //expand profile to necessary size
      unsigned oldSize=(unsigned)profile.size();
      profile.expand(unassignedCnt+1);
      for(unsigned pi=oldSize; pi<=unassignedCnt; pi++) {
	profile[pi]=0;
      }
    }
    profile[unassignedCnt]++;
  }
}

SATClauseIterator Preprocess::reorderVariablesByResolvability(unsigned varCnt, SATClauseIterator clauses)
{
  CALL("Preprocess::reorderVariablesByResolvability");

  static DArray<unsigned> order(128);
  static DArray<unsigned> permutation(128);
  static DArray<unsigned> bestProf(128);
  static DArray<unsigned> currProf(128);
  static DArray<SATClauseList*> clsByVar(128);
  clsByVar.init(varCnt, 0);

  SATClauseList* res=0;
  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();
    unsigned clen=cl->length();
    SATClauseList::push(cl, res);
    for(unsigned i=0;i<clen;i++) {
      SATClauseList::push(cl, clsByVar[(*cl)[i].var()]);
    }
  }

  order.initFromIterator(getRangeIterator(0u,varCnt), varCnt);
  Set<unsigned> fixed;
  for(unsigned currTgtVar=0;currTgtVar<varCnt-1;currTgtVar++) {
    unsigned var=order[currTgtVar];
    unsigned bestVarIndex=currTgtVar;
    createVarProfile(var, bestProf, clsByVar, fixed);
    for(unsigned vi=currTgtVar+1; vi<varCnt; vi++) {
      var=order[vi];
      createVarProfile(var, currProf, clsByVar, fixed);
      Comparison cmp=EQUAL;
      unsigned minProfSize=min(bestProf.size(), currProf.size());
      for(unsigned pi=0; cmp==EQUAL && pi<minProfSize; pi++) {
//      for(unsigned pi=1; cmp==EQUAL && pi<minProfSize; pi++) {
	cmp=Int::compare(bestProf[pi], currProf[pi]);
      }
      if(cmp==EQUAL) {
	cmp=Int::compare(bestProf.size(), currProf.size());
      }
      if(cmp==LESS || (cmp==EQUAL && Random::getBit())) {
	bestProf.initFromArray(currProf.size(), currProf);
	bestVarIndex=vi;
      }
      unsigned bestVar=order[bestVarIndex];
      fixed.insert(bestVar);
      std::swap(order[currTgtVar], order[bestVarIndex]);
    }
  }

  permutation.ensure(varCnt);
  for(unsigned i=0;i<varCnt;i++) {
    permutation[order[i]]=i;
  }
  return permutateVariables(varCnt, pvi( SATClauseList::DestructiveIterator(res) ), permutation.array());
}



SATClauseIterator Preprocess::randomizeVariables(unsigned varCnt, SATClauseIterator clauses)
{
  CALL("Preprocess::randomizeVariables");

  static DArray<unsigned> permutation(128);
  permutation.initFromIterator(getRangeIterator(0u,varCnt), varCnt);
  for(unsigned i=varCnt-1; i>0; i--) {
    unsigned tgtPos=Random::getInteger(i+1);
    std::swap(permutation[i], permutation[tgtPos]);
  }
  //now permutation contains a random permutation

  return permutateVariables(varCnt, clauses, permutation.array());
}

struct ConflictVarComparator
{
  ConflictVarComparator(unsigned* conflicts, unsigned varCnt)
  : _conflicts(conflicts), _varCnt(varCnt) {}

  float getConflictness(unsigned i) {
    if(_varCnt<3) {
      return _conflicts[i];
    }
    if(i==0) {
      return _conflicts[i]/((float)_conflicts[i+1]+1);
    } else if(i==_varCnt-1) {
      return _conflicts[i]/((float)_conflicts[i-1]+1);
    } else {
      return (2.0f*_conflicts[i])/(_conflicts[i-1]+_conflicts[i+1]+2);
    }
  }

  Comparison compare(unsigned i, unsigned j)
  { return Int::compare(getConflictness(j), getConflictness(i)); }

  unsigned* _conflicts;
  unsigned _varCnt;
};

SATClauseIterator Preprocess::reorderVariablesByConflicts(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* conflictCnts)
{
  CALL("Preprocess::reorderVariablesByConflicts");
  static DArray<unsigned> invPermutation(128);
  invPermutation.initFromIterator(getRangeIterator(0u,varCnt), varCnt);
  invPermutation.sort(ConflictVarComparator(conflictCnts, varCnt));

  static DArray<unsigned> permutation(128);
  permutation.ensure(varCnt);
  for(unsigned i=0;i<varCnt;i++) {
    permutation[invPermutation[i]]=i;
  }

  return permutateVariables(varCnt, clauses, permutation.array());
}

SATClauseIterator Preprocess::permutateVariables(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* permutation)
{
  CALL("Preprocess::permutateVariables");
#if VDEBUG
  //we check that we've been indeed given a permutation
  Set<unsigned> tgts;
  for(unsigned i=0;i<varCnt;i++) {
    unsigned tgt=permutation[i];
    ASS(!tgts.contains(tgt));
    tgts.insert(tgt);
  }
#endif
  //We don't care about collecting the proof yet, so we can do
  //the variable renaming in-place.
  SATClauseList* res=0;
  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral lit=(*cl)[i];
      (*cl)[i].set(permutation[lit.var()], lit.isPositive());
    }
    cl->sort();
    SATClauseList::push(cl, res);
  }

  return pvi( SATClauseList::DestructiveIterator(res) );
}


SATClauseIterator Preprocess::removeDuplicateLiterals(SATClauseIterator clauses)
{
  CALL("Preprocess::removeDuplicateLiterals");
  SATClauseList* res=0;
  while(clauses.hasNext()) {
    SATClause* cl=clauses.next();
    unsigned clen=cl->length();

    unsigned duplicate=0;
    for(unsigned i=1;i<clen;i++) {
      if((*cl)[i-1].var()==(*cl)[i].var()) {
	if((*cl)[i-1].polarity()==(*cl)[i].polarity()) {
	  std::swap((*cl)[duplicate], (*cl)[i]);
	  duplicate++;
	} else {
	  cl->destroy();
	  goto main_continue;
	}
      }
    }
    if(duplicate) {
      unsigned newLen=clen-duplicate;
      SATClause* cl2=new(newLen) SATClause(newLen, true);

      for(unsigned i=0;i<newLen;i++) {
        (*cl2)[i]=(*cl)[duplicate+i];
      }
      cl2->sort();
      cl=cl2;
    }

    SATClauseList::push(cl,res);
  main_continue: {}
  }
  return pvi( SATClauseList::DestructiveIterator(res) );
}

SATClauseIterator Preprocess::generate(unsigned literalsPerClause,
	unsigned varCnt, float clausesPerVariable)
{
  CALL("Preprocess::generate");

  unsigned clen=literalsPerClause;
  SATClauseList* res=0;
  unsigned litContMax=varCnt*2;

  unsigned remains=static_cast<unsigned>(varCnt*clausesPerVariable);
  while(remains-->0) {
    SATClause* cl=new(clen) SATClause(clen, true);

    for(unsigned i=0;i<clen;i++) {
      (*cl)[i].setContent(Random::getInteger(litContMax));
    }

    cl->sort();

    SATClauseList::push(cl,res);
  }
  return pvi( SATClauseList::DestructiveIterator(res) );
}

};
