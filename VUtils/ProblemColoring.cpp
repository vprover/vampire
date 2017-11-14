
/*
 * File ProblemColoring.cpp.
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
 * ProblemColoring.cpp
 */


#include "Debug/Tracer.hpp"

#include "Lib/BinaryHeap.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/MapToLIFO.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/UIHelper.hpp"


#include "ProblemColoring.hpp"

namespace VUtils
{

using namespace Lib;

using namespace Kernel;
using namespace Shell;

struct ProblemColoring::SymIdComparator
{
  //static variable is not a very nice way of doing this, but we just need to
  //quickly and simply fit into the BinaryHeap interface
  static DHMultiset<SymId>* gen;
  static Comparison compare(SymId s1, SymId s2)
  {
    CALL("ProblemColoring::SymIdComparator::compare");

    Comparison res=Int::compare(gen->multiplicity(s1), gen->multiplicity(s2));
    if(res==EQUAL) {
      res=Int::compare(s1,s2);
    }
    return res;
  }
};

DHMultiset<ProblemColoring::SymId>* ProblemColoring::SymIdComparator::gen;


/**
 * Try to assign different colors to symbols of a problem.
 * Return 0 if both left and right color could be assigned to
 * at least one symbol; otherwise return 1.
 */
int ProblemColoring::perform(int argc, char** argv)
{
  CALL("ProblemColoring::perform");

  //remove the first argument
  argc--; argv++;

  Shell::CommandLine cl(argc,argv);
  cl.interpret(*env.options);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  DHMultiset<SymId> generality; //contains number of symbol occurences


  Stack<SymId> syms;
  UnitList::Iterator uit(prb->units());
  while(uit.hasNext()) {
    Unit* u=uit.next();
    syms.reset();
    syms.loadFromIterator(symEx.extractSymIds(u));

    Stack<SymId>::Iterator sit1(syms);
    while(sit1.hasNext()) {
      SymId s1=sit1.next();
      generality.insert(s1);

      Stack<SymId>::Iterator sit2(syms);
      while(sit2.hasNext()) {
        SymId s2=sit2.next();
        if(s1==s2) {
          continue;
        }
        neigh.pushToKey(s1, s2);
      }
    }
  }

  //make a heap that will first give symbols that occur the least
  SymIdComparator::gen=&generality;
  BinaryHeap<SymId, SymIdComparator> orderedSyms;

  SymId symIdBound=symEx.getSymIdBound();
  //we start from 1 as 0 is equality
  for(SymId i=1;i<symIdBound;i++) {
    if(!symEx.validSymId(i)) {
      continue;
    }
    orderedSyms.insert(i);
  }


  //First try assign left and right colors in a fair manner to the least occurring symbols.
  //This way we expect to assign the most diverse colors to the most symbols.
  bool lastLeft=false;
  while(!orderedSyms.isEmpty()) {
    SymId i=orderedSyms.pop();
    ASS(symEx.validSymId(i));

    if(lastLeft) {
      if(tryAssignColor(i, RIGHT)) {
	lastLeft=false;
      }
    }
    else {
      if(tryAssignColor(i, LEFT)) {
	lastLeft=true;
      }
    }
  }

  //now assign all that can be assigned
  for(SymId i=1;i<symIdBound;i++) {
    if(!symEx.validSymId(i)) {
      continue;
    }
    if(!tryAssignColor(i, RIGHT)) {
      tryAssignColor(i, LEFT);
    }
  }

  bool assignedToSome[2]={false, false};

  env.beginOutput();
  for(int cIndex=0;cIndex<2;cIndex++) {
    const char* const cstr=(cIndex==0)?"left":"right";
    Color reqCol=(cIndex==0)?LEFT:RIGHT;
    for(SymId i=1;i<symIdBound;i++) {
      if(!symEx.validSymId(i)) {
	continue;
      }
      Color c=symCols.get(i);
      if(c!=reqCol) {
	continue;
      }
      assignedToSome[cIndex]=true; //set a flag that this color has been used
      bool pred;
      unsigned functor;
      symEx.decodeSymId(i, pred, functor);
      if(pred) {
	env.out()<<"vampire(symbol,predicate,"
	    <<env.signature->predicateName(functor)<<","
	    <<env.signature->predicateArity(functor)<<","<<cstr<<")."<<endl;
      }
      else {
	env.out()<<"vampire(symbol,function,"
	    <<env.signature->functionName(functor)<<","
	    <<env.signature->functionArity(functor)<<","<<cstr<<")."<<endl;
      }
    }
  }

  env.out()<<endl;


  for(int cIndex=0;cIndex<3;cIndex++) {
    Color reqColor=(cIndex==0)?LEFT:(cIndex==1?RIGHT:TRANSPARENT);
    if(cIndex<2) {
      const char* const cstr=(cIndex==0)?"left":"right";
      env.out()<<"vampire("<<cstr<<"_formula)."<<endl;
    }

    uit=UnitList::Iterator(prb->units());
    while(uit.hasNext()) {
      Unit* u=uit.next();
      if(getUnitColor(u)!=reqColor) {
	continue;
      }
      env.out()<<TPTPPrinter::toString(u)<<endl;
    }
    if(cIndex<2) {
      env.out()<<"vampire(end_formula)."<<endl<<endl<<endl;
    }
  }

  env.endOutput();

  return (assignedToSome[0] && assignedToSome[1]) ? 0 : 1;
}

bool ProblemColoring::tryAssignColor(SymId sym, Color c)
{
  CALL("ProblemColoring::assignColor");

  ASS(c==LEFT || c==RIGHT);

  Color oldCol=symCols.get(sym, ANY);

  if( oldCol==TRANSPARENT ||
      (c==LEFT && (oldCol==RIGHT || oldCol==NOLEFT))  ||
      (c==RIGHT && (oldCol==LEFT || oldCol==NORIGHT)) ) {
    return false;
  }

  if(c==oldCol) {
    return true;
  }

  SymIdIterator nit=pvi( neigh.keyIterator(sym) );

  while(nit.hasNext()) {
    SymId n=nit.next();
    Color ncol=symCols.get(n, ANY);
    if( (c==LEFT && ncol==RIGHT) ||
	(c==RIGHT && ncol==LEFT)) {
      return false;
    }
  }

  symCols.set(sym, c);

  nit=pvi( neigh.keyIterator(sym) );

  while(nit.hasNext()) {
    SymId n=nit.next();
    Color ncol=symCols.get(n, ANY);
    if(c==LEFT) {
      if(ncol==ANY) {
	symCols.set(n, NORIGHT);
      }
      else if(ncol==NOLEFT) {
	symCols.set(n, TRANSPARENT);
      }
    }
    else {
      ASS_EQ(c, RIGHT);
      if(ncol==ANY) {
	symCols.set(n, NOLEFT);
      }
      else if(ncol==NORIGHT) {
	symCols.set(n, TRANSPARENT);
      }
    }
  }

  return true;
}

ProblemColoring::Color ProblemColoring::getUnitColor(Unit* u)
{
  CALL("ProblemColoring::getUnitColor");

  Color res=TRANSPARENT;
  SymIdIterator syms=symEx.extractSymIds(u);
  while(syms.hasNext()) {
    SymId s=syms.next();
    Color c=symCols.get(s);
    if(c==LEFT || c==RIGHT) {
      ASS(res==c || res==TRANSPARENT);
      res=c;
    }
  }
  return res;
}


}
