/**
 * @file DIMACS.cpp
 * Implements class DIMACS.
 */


#include <iostream>
#include <fstream>

#include "../Lib/BinaryHeap.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/List.hpp"
#include "../Lib/MapToLIFO.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"

#include "DIMACS.hpp"

namespace SAT
{

using namespace std;
using namespace Lib;

void DIMACS::outputGroundedProblem(MapToLIFO<Clause*, SATClause*>& insts,
	  SATClause::NamingContext& nctx, ostream& out)
{
  CALL("DIMACS::outputGroundedProblem");

  unsigned cnt, maxVar;
  getStats(insts.allValIterator(), cnt, maxVar);
  out<<"p cnf "<<maxVar<<"  "<<cnt<<endl;

  BinaryHeap<int, Int> vnums;
  DHMap<int, Literal*, IdentityHash> vasgn(nctx.map);

  MapToLIFO<Clause*, SATClause*>::KeyIterator cls(insts);
  while(cls.hasNext()) {
    Clause* cl=cls.next();
    ASS(vnums.isEmpty());

    //we put all used prop. variables into vnums...
    SATClauseList* gcls=insts.keyVals(cl);
    SATClauseList::Iterator git(gcls);
    while(git.hasNext()) {
      SATClause* gcl=git.next();
      unsigned glen=gcl->length();
      for(unsigned i=0;i<glen;i++) {
	vnums.insert((*gcl)[i].var());
      }
    }
    //...and print them ordered.
    while(!vnums.isEmpty()) {
      int vnum=vnums.popWithAllEqual();
      out<<"% "<<vnum<<": "<<(vasgn.get(vnum)->toString())<<endl;
    }

    out<<"% Grounding "<<cl->nonPropToString()<<endl;
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

void DIMACS::outputProblem(SATClauseList* clauses, ostream& out)
{
  CALL("DIMACS::outputProblem");

  unsigned cnt, maxVar;
  getStats(pvi( SATClauseList::Iterator(clauses) ), cnt, maxVar);
  out<<"p cnf "<<maxVar<<"  "<<cnt<<endl;

  SATClauseList::Iterator cit(clauses);
  while(cit.hasNext()) {
    SATClause* cl=cit.next();
    out<<cl->toDIMACSString()<<endl;
  }
  out<<"0"<<endl;
}

SATClauseIterator DIMACS::parse(const char* fname, unsigned& maxVar)
{
  CALL("DIMACS::parse");

  istream* inp0;

  if(fname) {
    inp0=new ifstream(fname);
  } else {
    inp0=&cin;
  }

  istream& inp=*inp0;
  if(!inp.good()) {
    cout<<"Cannot open file\n";
    exit(0);
  }

  char buf[512];
  char ch;
  inp>>ch;
  while(ch=='c') {
    inp.getline(buf,512);
    inp>>ch;
  }
  ASS_EQ(ch,'p');
  for(int i=0;i<3;i++) {
    inp>>ch;
  }

  SATClauseList* res=0;

  unsigned remains;
  int ivar;
  Stack<int> vars(64);
  inp>>maxVar;
  inp>>remains;
  while(remains--) {
    inp>>ivar;
    while(ivar!=0) {
      if(inp.eof()) {
	cout<<"Invalid input\n";
	exit(0);
      }
      vars.push(ivar);
      inp>>ivar;
    }
    unsigned clen=(unsigned)vars.size();
    SATClause* cl=new(clen) SATClause(clen, true);
    for(int i=(int)clen-1; i>=0;i--) {
      ivar=vars.pop();
      (*cl)[i].set(abs(ivar), ivar>0);
    }
    ASS(vars.isEmpty());

    cl->sort();
    SATClauseList::push(cl,res);
  }

  if(inp0!=&cin) {
    delete inp0;
  }

  return pvi( SATClauseList::DestructiveIterator(res) );
}


}
