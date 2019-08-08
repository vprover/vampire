
/*
 * File KBO.cpp.
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
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include <Kernel/TermIterators.hpp>
#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/DHMultiset.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "SKIKBO.hpp"
#include "Signature.hpp"
#include "SortHelper.hpp"
#include "ApplicativeHelper.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

typedef ApplicativeHelper AH;

/**
 * Create a KBO object.
 */
SKIKBO::SKIKBO(Problem& prb, const Options& opt)
 : PrecedenceOrdering(prb, opt)
{
  CALL("SKIKBO::SKIKBO");

  _variableWeight = 1;
  _defaultSymbolWeight = 1;
}

SKIKBO::~SKIKBO()
{
  CALL("SKIKBO::~SKIKBO");
}


SKIKBO::VarCondRes SKIKBO::compareVariables(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compareVariables");

  VarCondRes vcr = BOTH;

  DHMultiset<Term*> tl1UnstableTerms;
  VarOccMap tl1RedData;
  DHMultiset<Term*> tl2UnstableTerms;
  VarOccMap tl2RedData;

  if(!tl1.isVar()){
    UnstableSubTermIt usti(tl1.term());
    while(usti.hasNext()){
      tl1UnstableTerms.insert(usti.next());
    }
  }

  if(!tl2.isVar()){
    UnstableSubTermIt usti(tl2.term());
    while(usti.hasNext()){
      tl2UnstableTerms.insert(usti.next());
    }
  }

  if(tl1UnstableTerms.size() > tl2UnstableTerms.size()){
    vcr = LEFT;
  } else if (tl2UnstableTerms.size() > tl1UnstableTerms.size()){
    vcr = RIGHT;
  }

  DHMultiset<Term*>::SetIterator tl1utit(tl1UnstableTerms);
  while(tl1utit.hasNext()){
    unsigned tl1Mult = 0;
    Term* t = tl1utit.next(tl1Mult);
    unsigned tl2Mult = tl2UnstableTerms.multiplicity(t);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
      break;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<Term*>::SetIterator tl2utit(tl2UnstableTerms);
  while(tl2utit.hasNext()){
    unsigned tl2Mult = 0;
    Term* t = tl2utit.next(tl2Mult);
    unsigned tl1Mult = tl1UnstableTerms.multiplicity(t);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
      break;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<unsigned> tl1vars;
  StableVarIt svi(tl1, &tl1UnstableTerms);
  while(svi.hasNext()){
    TermList tl = svi.next();
    TermList head = ApplicativeHelper::getHead(tl);
    ASS(head.isVar());
    tl1vars.insert(head.var());
  }

  DHMultiset<unsigned> tl2vars;
  StableVarIt svi2(tl2, &tl2UnstableTerms);
  while(svi2.hasNext()){
    TermList tl = svi2.next();
    TermList head = ApplicativeHelper::getHead(tl);
    ASS(head.isVar());
    tl2vars.insert(head.var());
  }

  if(tl1vars.size() > tl2vars.size() && vcr != RIGHT){
    vcr = LEFT;
  } else if (tl2vars.size() > tl1vars.size()  && vcr != LEFT){
    vcr = RIGHT;
  } else if(tl1vars.size() != tl2vars.size()){
    return INCOMP;
  }


  DHMultiset<unsigned>::SetIterator tl1vit(tl1vars);
  while(tl1vit.hasNext()){
    unsigned tl1Mult = 0;
    unsigned var = tl1vit.next(tl1Mult);
    unsigned tl2Mult = tl2vars.multiplicity(var);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
      break;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<unsigned>::SetIterator tl2vit(tl2vars);
  while(tl2vit.hasNext()){
    unsigned tl2Mult = 0;
    unsigned var = tl2vit.next(tl2Mult);
    unsigned tl1Mult = tl1vars.multiplicity(var);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
      break;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMap<unsigned, unsigned> varCounts;
  static TermStack args;
  StableVarIt svi3(tl1, &tl1UnstableTerms);
  while(svi3.hasNext()){
    args.reset(); //TODO required?
    TermList tl = svi3.next();
    TermList head;
    ApplicativeHelper::getHeadAndArgs(tl, head, args);
    ASS(head.isVar());
    unsigned var = head.var();
    DArray<DArray<unsigned>*>* vData;
    unsigned count;
    if(tl1RedData.find(var)){
      vData = tl1RedData.get(var);
      count = varCounts.get(var);
    } else {
      vData = new DArray<DArray<unsigned>*>(tl1vars.multiplicity(var));
      count = 0;
      tl1RedData.set(var, vData);
    }
    varCounts.set(var, count + 1);
    (*vData)[count] = new DArray<unsigned>(args.size());
    for(unsigned i = 0; i < args.size(); i++){
      (*(*vData)[count])[i] = getMaxRedLength(args.pop());
    }
  }

  varCounts.reset();
  StableVarIt svi4(tl2, &tl2UnstableTerms);
  while(svi4.hasNext()){
    args.reset(); //TODO required?
    TermList tl = svi4.next();
    TermList head;
    ApplicativeHelper::getHeadAndArgs(tl, head, args);
    ASS(head.isVar());
    unsigned var = head.var();
    DArray<DArray<unsigned>*>* vData;
    unsigned count;
    if(tl2RedData.find(var)){
      vData = tl2RedData.get(var);
      count = varCounts.get(var);
    } else {
      vData = new DArray<DArray<unsigned>*>(tl2vars.multiplicity(var));
      count = 0;
      tl2RedData.set(var, vData);
    }
    varCounts.set(var, count + 1);
    (*vData)[count] = new DArray<unsigned>(args.size()); //TODO why does this not trigger allocator bug?
    for(unsigned i = 0; i < args.size(); i++){
      (*(*vData)[count])[i] = getMaxRedLength(args.pop());
    }
  }

  vcr =  compareVariables(tl1RedData, tl2RedData, vcr);
  //freeMem(tl1RedData, tl2RedData);
  return vcr;
}

SKIKBO::VarCondRes SKIKBO::compareVariables(VarOccMap& vomtl1 , VarOccMap& vomtl2, VarCondRes currStat) const
{
  CALL("SKIKBO::compareVariables/2");

  if(currStat == LEFT || currStat == BOTH){
    VarOccMap::Iterator it1(vomtl2);
    while(it1.hasNext()){
      unsigned var;
      DArray<DArray<unsigned>*>* arrtl2 = it1.nextRef(var);
      ASS(vomtl1.find(var));
      DArray<DArray<unsigned>*>* arrtl1 = vomtl1.get(var); //returned by ref
      
      unsigned m = arrtl2->size();
      unsigned n = arrtl1->size();

      DArray<DArray<bool>> bpGraph;
      bpGraph.ensure(m);
      for(unsigned i = 0; i < m; i++){
        DArray<unsigned>* redLengths2 = (*arrtl2)[i]; 
        bpGraph[i].ensure(n);
        for(unsigned j = 0; j < n; j++){
          DArray<unsigned>* redLengths1 = (*arrtl1)[j]; 
          bpGraph[i][j] = canBeMatched(redLengths2, redLengths1);
        }
      }
      if(!totalBMP(m, n, bpGraph)){
        if(currStat == LEFT){ return INCOMP; }
        currStat = RIGHT;
        break;
      }
    }
  }
  
  if(currStat == LEFT){ return LEFT; }

  VarOccMap::Iterator it2(vomtl1);
  while(it2.hasNext()){
    unsigned var;
    DArray<DArray<unsigned>*>* arrtl1 = it2.nextRef(var);
    ASS(vomtl2.find(var));
    DArray<DArray<unsigned>*>* arrtl2 = vomtl2.get(var); //returned by ref
    
    unsigned m = arrtl1->size();
    unsigned n = arrtl2->size();

    DArray<DArray<bool>> bpGraph;
    bpGraph.ensure(m);
    for(unsigned i = 0; i < m; i++){
      DArray<unsigned>* redLengths2 = (*arrtl1)[i]; 
      bpGraph[i].ensure(n);
      for(unsigned j = 0; j < n; j++){
        DArray<unsigned>* redLengths1 = (*arrtl2)[j]; 
        bpGraph[i][j] = canBeMatched(redLengths2, redLengths1);
      }
    }
    if(!totalBMP(m, n, bpGraph)){
      if(currStat == RIGHT){ return INCOMP; }
      currStat = LEFT;
      break;
    }
  }
  return currStat; 
}

void SKIKBO::freeMem(VarOccMap& vomtl1 , VarOccMap& vomtl2) const
{
  CALL("SKIKBO::freeMem");

  VarOccMap::Iterator it1(vomtl2);
  while(it1.hasNext()){
    DArray<DArray<unsigned>*>* arr = it1.next();
    delete arr;
  }

  VarOccMap::Iterator it2(vomtl2);
  while(it2.hasNext()){
    DArray<DArray<unsigned>*>* arr = it2.next();
    delete arr;
  }
}

bool SKIKBO::canBeMatched(DArray<unsigned>* redLengths1, DArray<unsigned>* redLengths2) const
{
  CALL("SKIKBO::canBeMatched");

  for(unsigned i = 0; i < redLengths1->size(); i++){
    if(i < redLengths2->size()){
      if((*redLengths1)[i] > (*redLengths2)[i]){
        return false;
      } 
    } else if((*redLengths1)[i] > 0){
      return false;
    }
  }
  return true;
}

bool SKIKBO::bpm(unsigned n, DArray<DArray<bool>>& bpGraph, int u, 
         DArray<bool>& seen , DArray<int>& matchR) const
{ 
  CALL("SKIKBO::bpm");

  for (int v = 0; v < n; v++) 
  { 
    if (bpGraph[u][v] && !seen[v]) 
    { 
      seen[v] = true;  
      if (matchR[v] < 0 || bpm(n, bpGraph, matchR[v], seen, matchR)) 
      { 
        matchR[v] = u; 
        return true; 
      } 
    } 
  } 
  return false; 
} 
  
bool SKIKBO::totalBMP(unsigned m, unsigned n, DArray<DArray<bool>>& bpGraph) const
{ 
  CALL("SKIKBO::totalBMP");
  
  DArray<int> matchR;
  matchR.init(n, -1);

  for (int u = 0; u < m; u++) 
  { 
    DArray<bool> seen;
    seen.init(n, 0);

    if (!bpm(n, bpGraph, u, seen, matchR)){return false;} 
  } 
  return true; 
}

unsigned SKIKBO::getMaxRedLength(TermList t) const
{
  CALL("SKIKBO::getMaxRedLength");

  if(t.isVar()){ return  0; }

  int tRedLen = t.term()->maxRedLength();
  if(tRedLen == -1){
    tRedLen = maximumReductionLength(t.term());
    t.term()->setMaxRedLen(tRedLen);
  }
  return (unsigned)tRedLen;
}


Ordering::Result SKIKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }

  VarCondRes varCond = compareVariables(tl1, tl2);

  if(varCond == INCOMP){ return INCOMPARABLE; }
  
  unsigned tl1RedLen = getMaxRedLength(tl1);
  unsigned tl2RedLen = getMaxRedLength(tl2);
  if((varCond == LEFT  || varCond == BOTH) && tl1RedLen > tl2RedLen){
    return GREATER;
  } 
  if((varCond == RIGHT  || varCond == BOTH) && tl2RedLen > tl1RedLen){
    return LESS;
  }
  if(tl1RedLen != tl2RedLen){
    return INCOMPARABLE;
  }
  
  unsigned tl1Weight = tl1.isVar() ? 1 : tl1.term()->weight(); //TODO wrong weight
  unsigned tl2Weight = tl2.isVar() ? 1 : tl2.term()->weight();
  if((varCond == LEFT  || varCond == BOTH) && tl1Weight > tl2Weight){
    return GREATER;
  } 
  if((varCond == RIGHT  || varCond == BOTH) && tl2Weight > tl1Weight){
    return LESS;
  }
  if(tl2Weight != tl1Weight){
    return INCOMPARABLE;
  }  

  static TermStack args1;
  static TermStack args2;
  args1.reset();
  args2.reset();
  TermList head1;
  TermList head2;

  AH::getHeadAndArgs(tl1, head1, args1);
  AH::getHeadAndArgs(tl2, head2, args2);
  if(head1.isTerm() && head2.isTerm()){ //TODO is this OK?
    Ordering::Result res = compareFunctionPrecedences(head1.term()->functor(), head2.term()->functor());
    if((varCond == LEFT  || varCond == BOTH) && res == GREATER){
      return GREATER;
    } 
    if((varCond == RIGHT  || varCond == BOTH) && res == LESS){
      return LESS;
    }
    if(head1.term()->functor() != head2.term()->functor()){
      return INCOMPARABLE;
    } 
  }

  if((varCond == LEFT  || varCond == BOTH) && args1.size() > args2.size()){
    return GREATER;
  } 
  if((varCond == RIGHT  || varCond == BOTH) && args1.size() < args2.size()){
    return LESS;
  }
  if(args1.size() != args2.size()){
    return INCOMPARABLE;
  } 

  //TODO unary functions of weight 0 not dealt with
  for(unsigned i = args1.size() -1; i >= 0; i--){
    Ordering::Result res = compare(args1[i], args2[i]); //TODO recursive call should be to hzkbo
    if((varCond == LEFT  || varCond == BOTH) && res == GREATER){
      return GREATER;
    } 
    if((varCond == RIGHT  || varCond == BOTH) && res == LESS){
      return LESS;
    }
    if(res != EQUAL){
      return INCOMPARABLE;
    } 
  }


}

int SKIKBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;

  return weight;
}


unsigned SKIKBO::maximumReductionLength(Term* term)
{
  CALL("SKIKBO::maximumReductionLength");  
   
  typedef SortHelper SH;  
  
  static Stack<Term*> toEvaluate;
  static TermStack args;
  TermList head;
  unsigned length = 0;

  auto addToEvaluate = [&toEvaluate] (TermList t) { 
    if(!t.isVar()){
      toEvaluate.push(t.term());
    }
  }; 

  toEvaluate.push(term);
  while(!toEvaluate.isEmpty()){
    args.reset(); 
    Term* evaluating = toEvaluate.pop();
    AH::getHeadAndArgs(evaluating, head, args);
    if(!AH::isComb(head) || AH::isUnderApplied(head, args.size())){
      while(!args.isEmpty()){
        addToEvaluate(args.pop());
      }
    } else {
      Signature::Combinator c = AH::getComb(head);
      TermList newHeadSort = AH::getNthArg(SH::getResultSort(head.term()), 1);
      if(c == Signature::I_COMB){
        addToEvaluate(AH::createAppTerm(newHeadSort, args.pop(), args));//working on the assumption that the pop happens first...
        length++;
      } else if(c == Signature::K_COMB){
        TermList newHead = args.pop();
        addToEvaluate(args.pop()); 
        addToEvaluate(AH::createAppTerm(newHeadSort, newHead, args));
        length++;
      } else {
        length++;
        addToEvaluate(reduce(args, head));
      }
    }
  }
  return length;
}

TermList SKIKBO::reduce(TermStack& args, TermList& head)
{
  CALL("SKIKBO::reduce");
  
  ASS(head.isTerm());
  
  TermList headSort = SortHelper::getResultSort(head.term());
  
  TermList newHeadSort = ApplicativeHelper::getNthArg(headSort, 1);
  TermList newHead = args.pop();

  TermList sort2 = ApplicativeHelper::getNthArg(headSort, 2);
  
  switch(ApplicativeHelper::getComb(head)){
    case Signature::C_COMB: {
      TermList temp = args[args.size() -1];
      args[args.size() - 1] = args[args.size() -  2];
      args[args.size() - 2] = temp;
      break;
    }
    case Signature::B_COMB: {
      args.push(ApplicativeHelper::createAppTerm(sort2, args.pop(), args.pop()));
      break;      
    }
    case Signature::S_COMB: {
      TermList y = args.pop();
      TermList z = args.pop();
      args.push(ApplicativeHelper::createAppTerm(sort2, y, z));
      args.push(z);
    }
    default:
      ASSERTION_VIOLATION; 
  }
  return ApplicativeHelper::createAppTerm(newHeadSort, newHead, args);;  
}


}
