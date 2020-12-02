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
 * @file DIMACS.cpp
 * Implements class DIMACS.
 */


#include <iostream>

#include "Lib/BinaryHeap.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"

#include "DIMACS.hpp"

namespace SAT
{

using namespace std;
using namespace Lib;

void DIMACS::outputGroundedProblem(MapToLIFO<Clause*, SATClause*>& insts,
	  SATClause::NamingContext& nctx, ostream& out)
{
  CALL("DIMACS::outputGroundedProblem");

  bool outputComments = false;

  unsigned cnt, maxVar;
  getStats(insts.allValIterator(), cnt, maxVar);
  out<<"p cnf "<<maxVar<<"  "<<cnt<<endl;

  BinaryHeap<int, Int> vnums;
  DHMap<int, Literal*, IdentityHash> vasgn;
  vasgn.loadFromInverted(nctx.map);

  MapToLIFO<Clause*, SATClause*>::KeyIterator cls(insts);
  while(cls.hasNext()) {
    Clause* cl=cls.next();
    // ASS(vnums.isEmpty());

    //we put all used prop. variables into vnums...
    SATClauseList* gcls=insts.keyVals(cl);
    SATClauseList::Iterator git(gcls);
    while(git.hasNext()) {
      SATClause* gcl=git.next();
      unsigned glen=gcl->length();
      if(outputComments) {
	for(unsigned i=0;i<glen;i++) {
	  vnums.insert((*gcl)[i].var());
	}
      }
    }
    if(outputComments) {
      //...and print them ordered.
      while(!vnums.isEmpty()) {
	int vnum=vnums.popWithAllEqual();
	out<<"% "<<vnum<<": "<<(vasgn.get(vnum)->toString())<<endl;
      }
      out<<"% Grounding "<<cl->literalsOnlyToString()<<endl;
    }

    SATClauseList::Iterator git2(gcls);
    while(git2.hasNext()) {
      SATClause* gcl=git2.next();
      out<<gcl->toDIMACSString()<<endl;
    }
  }
  out<<"%"<<endl<<"0"<<endl;
}

void DIMACS::getStats(SATClauseIterator clauses, unsigned& clauseCnt, unsigned& maxVar)
{
  clauseCnt=0;
  maxVar=0;
  while(clauses.hasNext()) {
    clauseCnt++;
    SATClause* cl=clauses.next();
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      ASS_G((*cl)[i].var(),0);
      if((*cl)[i].var()>maxVar) {
	maxVar=(*cl)[i].var();
      }
    }
  }
}
}
