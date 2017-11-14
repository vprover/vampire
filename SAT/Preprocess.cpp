
/*
 * File Preprocess.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

#include "Lib/Comparison.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Statistics.hpp"

#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Preprocess.hpp"

#undef LOGGING
#define LOGGING 1

namespace SAT
{

using namespace Lib;

/**
 * Filter out clauses with literals that appear only with one polarity. @b varCnt must be greater
 * than all variable numbers.
 */
SATClauseIterator Preprocess::filterPureLiterals(unsigned varCnt, SATClauseIterator clauses)
{
  CALL("Preprocess::filterPureLiterals(unsigned,SATClauseIterator)");

  SATClauseList* lst=0;
  SATClauseList::pushFromIterator(clauses, lst);
  filterPureLiterals(varCnt, lst);
  return pvi( SATClauseList::DestructiveIterator(lst) );
}

/**
 * Filter out clauses with literals that appear only with one polarity. @b varCnt must be greater
 * than all variable numbers.
 */
bool Preprocess::filterPureLiterals(unsigned varCnt, SATClauseList*& res)
{
  CALL("Preprocess::filterPureLiterals(unsigned,SATClauseList*&)");

  static Stack<unsigned> pureVars(64);
  static DArray<int> positiveOccurences(128);
  static DArray<int> negativeOccurences(128);
  static DArray<SATClauseList*> occurences(128);

  // variables start from 1, but we want to use them as indexes to zero based arrays
  // current solution: add one extra (unused) slot
  positiveOccurences.init(varCnt+1, 0);
  negativeOccurences.init(varCnt+1, 0);
  occurences.init(varCnt+1, 0);

  SATClauseList::Iterator cit(res);
  while(cit.hasNext()) {
    SATClause* cl=cit.next();

    cl->setKept(true);
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral lit=(*cl)[i];
      unsigned var=lit.var();
      ASS_G(var,0);
      SATClauseList::push(cl,occurences[var]);
      if(lit.isPositive()) {
	positiveOccurences[var]++;
      } else {
	negativeOccurences[var]++;
      }
    }
  }

  for(unsigned i=1;i<=varCnt;i++) {
    if( ((positiveOccurences[i]!=0)^(negativeOccurences[i]!=0)) && occurences[i] ) {
      pureVars.push(i);
      env.statistics->satPureVarsEliminated++;
    }
  }

  if(pureVars.isEmpty()) {
    return false;
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
	ASS_G(lvar,0);
	if(lit.isPositive()) {
	  positiveOccurences[lvar]--;
	  if( positiveOccurences[lvar]==0 && negativeOccurences[lvar]!=0 && occurences[lvar] ) {
	    pureVars.push(lvar);
	    env.statistics->satPureVarsEliminated++;
	  }
	} else {
	  negativeOccurences[lvar]--;
	  if( positiveOccurences[lvar]!=0 && negativeOccurences[lvar]==0 && occurences[lvar] ) {
	    pureVars.push(lvar);
	    env.statistics->satPureVarsEliminated++;
	  }
	}
      }
    }

  }

  ASS(SATClauseList::isEmpty(occurences[0]));
  for(unsigned i=1;i<=varCnt;i++) {
    SATClauseList::destroy(occurences[i]);
  }

#if VDEBUG
  bool someDeleted = false;
#endif
  SATClauseList::DelIterator rit(res);
  while(rit.hasNext()) {
    SATClause* cl=rit.next();
    if(!cl->kept()) {
      rit.del();
#if VDEBUG
      someDeleted = true;
#endif
    }
  }
  ASS(someDeleted);

  return true;
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
	  SATClauseList::destroy(res);
          SATClauseList::destroy(units);
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

/*
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
*/

SATClauseIterator Preprocess::permutateVariables(unsigned varCnt, SATClauseIterator clauses,
	  unsigned* permutation)
{
  CALL("Preprocess::permutateVariables");
#if VDEBUG
  //we check that we've been indeed given a permutation
  Set<unsigned> tgts;
  for(unsigned i=0;i<=varCnt;i++) {
    unsigned tgt=permutation[i];
    ASS(!tgts.contains(tgt));
    tgts.insert(tgt);
  }
  // which must be the identity for the unused 0 slot
  ASS_EQ(permutation[0],0);
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

/**
 * If clause is a tautology, destroy it and return 0.
 * If clause contains duplicate literals, remove them and return
 * modified clause.
 * If none of the above applies, return the original clause object,
 * possibly with modified literal order.
 *
 * If we're removing a duplicate literal and @c cl contains an inference
 * object, create inference for the new clause as well. If it does not
 * have inference object, destroy the original clause.
 */
SATClause* Preprocess::removeDuplicateLiterals(SATClause* cl)
{
  CALL("Preprocess::removeDuplicateLiterals(SATClause*)");

  unsigned clen=cl->length();

  cl->sort();

  unsigned duplicate=0;
  for(unsigned i=1;i<clen;i++) {
    if((*cl)[i-1].var()==(*cl)[i].var()) {
	if((*cl)[i-1].polarity()==(*cl)[i].polarity()) {
	  //We must get rid of the first occurrence of the duplicate (at i-1). Removing
	  //the second would make us miss the case when there are three duplicates.
	  std::swap((*cl)[duplicate], (*cl)[i-1]);
	  duplicate++;
	} else {
	  //delete tautology clauses
	  cl->destroy();
	  return 0;
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
    if(cl->inference()) {
	SATInference* cl2Inf = new PropInference(cl);
	cl2->setInference(cl2Inf);
    }
    else {
      cl->destroy();
    }
    cl=cl2;
  }
  return cl;
}

/**
 * Remove duplicate literals from clauses and delete tautology clauses.
 *
 * This transformation doesn't preserve order of variables in clauses.
 */
SATClauseIterator Preprocess::removeDuplicateLiterals(SATClauseIterator clauses)
{
  CALL("Preprocess::removeDuplicateLiterals(SATClauseIterator)");
  SATClauseList* res=0;
  while(clauses.hasNext()) {
    SATClause* cl=removeDuplicateLiterals(clauses.next());
    if(cl) {
      SATClauseList::push(cl,res);
    }
  }
  return pvi( SATClauseList::DestructiveIterator(res) );
}

SATClauseIterator Preprocess::generate(unsigned literalsPerClause,
	unsigned varCnt, float clausesPerVariable)
{
  CALL("Preprocess::generate");

  unsigned clen=literalsPerClause;
  SATClauseList* res=0;

  unsigned remains=static_cast<unsigned>(varCnt*clausesPerVariable);
  while(remains-->0) {
    SATClause* cl=new(clen) SATClause(clen, true);

    for(unsigned i=0;i<clen;i++) {
      (*cl)[i].set(Random::getInteger(varCnt)+1,Random::Random::getBit());
    }

    cl->sort();

    SATClauseList::push(cl,res);
  }
  return pvi( SATClauseList::DestructiveIterator(res) );
}

};
