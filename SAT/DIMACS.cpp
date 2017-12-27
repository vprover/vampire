
/*
 * File DIMACS.cpp.
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
 * @file DIMACS.cpp
 * Implements class DIMACS.
 */


#include <iostream>
#include <fstream>

#include "Lib/BinaryHeap.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

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
}

template <class T>
static T readT(istream& str, bool survive_eof = false) {
  T res;
  str >> res;
  if (str.fail() && !(survive_eof && str.eof())) {
    cout << "Invalid input.\n";
    exit(0);
  }
  return res;
}

SATClauseList* DIMACS::parse(const char* fname, unsigned& maxVar)
{
  CALL("DIMACS::parse");

  istream* inp0;

  if(fname) {
    // CAREFUL: this might not be enough if the ifstream (re)allocates while being operated
    BYPASSING_ALLOCATOR;
    
    inp0=new ifstream(fname);
  } else {
    inp0=&cin;
  }

  istream& inp=*inp0;
  if(!inp.good()) {
    cout<<"Cannot open file.\n";
    exit(0);
  }

  char ch = readT<char>(inp);
  while(ch=='c') {
    inp.ignore(numeric_limits<streamsize>::max(),'\n');
    ch = readT<char>(inp);
  }
  // the line should look like "p cnf #vars #clauses" ...
  if (ch != 'p') {
    cout<<"Invalid input: 'p' expected.\n";
  }
  // skip one more word -- should be "cnf"
  readT<char>(inp);
  inp.ignore(numeric_limits<streamsize>::max(),' ');
  unsigned num_vars = readT<unsigned>(inp);
  unsigned num_cls = readT<unsigned>(inp);
  
  SATClauseList* res=0;
  Stack<int> vars(64);
  
  unsigned numCls = 0;
  maxVar = 0;  
  
  int lit = readT<int>(inp,true);
  while (!inp.eof()) {  
    while (lit != 0) {            
      unsigned var = abs(lit);
      if (var > maxVar)
        maxVar = var;      
      vars.push(lit);            
      lit = readT<int>(inp);
    }
    
    lit = readT<int>(inp,true);
    
    numCls++;
    unsigned clen=(unsigned)vars.size();
    SATClause* cl=new(clen) SATClause(clen, true);
    for(int i=(int)clen-1; i>=0;i--) {
      int l = vars.pop();
      (*cl)[i].set(abs(l), l>0);
    }
    ASS(vars.isEmpty());

    SATClauseList::push(cl,res);
  }

  if (num_vars != maxVar)
    cout << "Warning: DIMACS input mis-specifies the number of variables (" 
            << num_vars << " specified and " << maxVar << " read).\n";
  if (num_cls != numCls)
    cout << "Warning: DIMACS input mis-specifies the number of clauses (" 
            << num_cls << " specified and " << numCls << " read).\n";
  
  if(inp0!=&cin) {
    BYPASSING_ALLOCATOR;
    
    delete inp0;
  }

  return res;
}


}
