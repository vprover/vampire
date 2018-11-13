
/*
 * File HOSortHelper.cpp.
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
 * @file HOSortHelper.cpp
 * Implements class HOSortHelper.
 */

#include "Lib/Environment.hpp"

#include "Clause.hpp"
#include "FormulaUnit.hpp"
#include "Signature.hpp"
#include "Sorts.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "HOSortHelper.hpp"
#include "SortHelper.hpp"
#include "Shell/LambdaElimination.hpp"
#include "Lib/SmartPtr.hpp"

using namespace Kernel;

/** 
 * Returns the sort of the head of an applicative term 
 * Cannot be called on a variable
 */
unsigned HOSortHelper::getHeadSort(TermList ts){
  CALL("HOSortHelper::getHeadSort");
  
  ASS(! ts.isVar());

  unsigned tsSort;
  Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
  while(sym->hOLAPP()){
    tsSort = SortHelper::getArgSort(ts.term(), 0);
    ts = *(ts.term()->nthArgument(0));
    if(ts.isVar()){ break; }
    sym = env.signature->getFunction(ts.term()->functor());
  }
  return tsSort;
}

TermList HOSortHelper::getNthArg(TermList ts, unsigned n){
  CALL("HOSortHelper::getNthArg");

  unsigned argnum = argNum(ts);
  if(argnum <= n){ ASSERTION_VIOLATION; }
  for(unsigned i = argnum; i > n+1; i--){
    ts = *(ts.term()->nthArgument(0));    
  }
  return *(ts.term()->nthArgument(1));  
}

//BAD CODE!
/** 
 * Returns the sort of the nth argument of the applicative term ts
 * argNum should be called prior to calling this function otherwise 
 * if n > argnum, an error will be thrown!
 */
unsigned HOSortHelper::getNthArgSort(TermList ts, unsigned n){
  CALL("HOSortHelper::getNthArgSort");

  unsigned argnum = argNum(ts);
  if(argnum <= n){ ASSERTION_VIOLATION; }
  for(unsigned i = argnum; i > n+1; i--){
    ts = *(ts.term()->nthArgument(0));    
  }
  ASS(ts.isTerm());
  //assuming getArgSort is 0 indexed
  return SortHelper::getArgSort(ts.term(), 1);  
}

/** 
 * Returns the number of args the head of an applicative term is applied to 
 */
unsigned HOSortHelper::argNum(TermList ts){
  CALL("HOSortHelper::argNum");
  
  unsigned arity = 0;
  
  if(ts.isVar()){
    return arity;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    while(sym->hOLAPP()){
      arity++;
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return arity;
      }
      sym = env.signature->getFunction(ts.term()->functor());
    }
    return arity;
  }  
  
}

/** 
 * Returns the resulting sort if a head of sort @b funcsort was to be applied to n arguments
 * If n is greater than arity of funcSort, the result sort is returned.
 */
unsigned HOSortHelper::appliedToN(unsigned funcSort, unsigned n){
  CALL("HOSortHelper::appliedToN");  
    
  for(unsigned i = 0; i < n; i++){
    if(env.sorts->isOfStructuredSort(funcSort, Sorts::StructuredSort::HIGHER_ORD_CONST)){
      funcSort = range(funcSort);
    } else { 
      break;
    }
  }
  return funcSort;
}

/** 
 * 
 */
unsigned HOSortHelper::appliedToN(TermList ts, unsigned n){
  CALL("HOSortHelper::appliedToN");  
  
  ASS(ts.isTerm());
  
  unsigned termSort = SortHelper::getResultSort(ts.term()); 
  return appliedToN(termSort, n);
}


/** 
 * Returns the nth argument sort of functional sort @b funcSort
 */
unsigned HOSortHelper::getNthArgSort(unsigned funcSort, unsigned n){
  CALL("HOSortHelper::getNthArgSort");  

  ASS(n >= 0);
  
  for(unsigned i = 0; i < n; i++){
    funcSort = range(funcSort);
  }
  return domain(funcSort);
}

/**
 * Returns the head symbol of an applicative term 
 */
//shouldn't really be here as not a sort function
TermList HOSortHelper::getHead(TermList ts){
  CALL("HOSortHelper::getHead");  
  
  if(ts.isVar()){
    return ts;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    while(sym->hOLAPP()){
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return ts;
      }
      sym = env.signature->getFunction(ts.term()->functor());
    }
    return ts;
  }
  
}

/** Takes two termlists and returns the result of applying the 
 *  first to the second. Sort conditions must be met
 */
TermList HOSortHelper::apply(TermList t1, unsigned s1, TermList t2, unsigned s2){
  CALL("HOSortHelper::apply");
  //cout << "t1 " + t1.toString() + " of sort " + env.sorts->sortName(s1) << endl;
  //cout << "t2 " + t2.toString() + " of sort " + env.sorts->sortName(s2) << endl;  
  
  ASS(arity(s1) > 0);
  ASS_REP(domain(s1) == s2 || (t2.isVar() && s2 == 0), 
    "t1 " + t1.toString() + " of sort " + env.sorts->sortName(s1) +
    "\nt2 " + t2.toString() + " of sort " + env.sorts->sortName(s2));

  TermList res;
  unsigned fun = LambdaElimination::introduceAppSymbol(s1, domain(s1), range(s1));
  LambdaElimination::buildFuncApp(fun, t1, t2, res);
  return res;
}

/**
  * Prints out HOTerm
  */
#if VDEBUG
vstring HOSortHelper::HOTerm::toString(bool withSorts, bool withIndices) const
{
  CALL("HOSortHelper::HOTerm::toString");   
  
  vstring res;
  if(!withSorts){
    vstring tween = (withIndices && head.isVar()) ? "/" + Int::toString(headInd) : "";
    res = head.toString() + tween +  " ";
  } else {
    res = head.toString() + "_" + env.sorts->sortName(headsort) + " ";
  }
  for(unsigned i = 0; i < args.size(); i++){
    if(!args[i]->args.size()){
      res = res + args[i]->toString(withSorts, withIndices);
    } else {
      res = res + "(" + args[i]->toString(withSorts, withIndices) + ")";
    }
  }
  return res;
}


vstring HOSortHelper::HOTerm::toStringWithTopLevelSorts(bool topLevel) const
{
  CALL("HOSortHelper::HOTerm::toStringWithTopLevelSorts");   
  
  vstring res = head.toString();
  if(topLevel){
   res = res + " of sort " + env.sorts->sortName(headsort) + " ";
  }
  
  for(unsigned i = 0; i < args.size(); i++){
    if(!args[i]->args.size()){
      if(topLevel){
        res = res + "\n arg" + Int::toString(i+1) + ":  ";
      }
      res = res + args[i]->toString(false);
      if(topLevel){
        res = res + " of sort " + env.sorts->sortName(args[i]->srt);
      }
    } else {
      if(topLevel){
        res = res + "\n arg" + Int::toString(i+1) + ":  ";
      }
      res = res + "(" + args[i]->toString(false) + ")";
      if(topLevel){
        res = res + " of sort " + env.sorts->sortName(args[i]->srt);
      }
    }
  }
  return res;
}
#endif


HOSortHelper::HOTerm_ptr HOSortHelper::createHOTerm(TermList head, int hsort, int index){
  CALL("HOSortHelper::createHOTerm/1"); 
  
  return HOTerm_ptr(new HOTerm(head, hsort, index));
}
  
/** creates a new HOTerm with same head and args as @b ht */
HOSortHelper::HOTerm_ptr HOSortHelper::createHOTerm(HOTerm_ptr ht){
  CALL("HOSortHelper::createHOTerm/2"); 

  return HOTerm_ptr(new HOTerm(*ht));
}

void HOSortHelper::HOTerm::headify(HOTerm_ptr tm){
  CALL("HOSortHelper::HOTerm::headify");   
 
  head = tm->head;
  headsort = tm->headsort;
  //srt = tm->srt;
  headInd = tm->headInd;
  for(int i = tm->args.size() - 1; i >=0; i--){
    args.push_front(tm->args[i]);
  }  
}


/**
 *  Converts a HOTerm struct into applicative form TermList
 */
TermList HOSortHelper::appify(HOTerm_ptr ht){
  CALL("HOSortHelper::appify");   

  #if VDEBUG
    //cout << "appifying " + ht->toString(false, true) << endl;
  #endif

  Stack<Stack<HOTerm_ptr>> toDo;
  Stack<TermList> done;
  Stack<unsigned> doneSorts;

  if(ht->args.isEmpty()){
    return ht->head;
  }

  done.push(ht->head);
  doneSorts.push(ht->headsort);

  Stack<HOTerm_ptr> hts;
  toDo.push(hts);
  
  for(int i = ht->args.size() - 1; i >=0; i--){
    toDo.top().push(ht->args[i]);
  }

  while(!toDo.isEmpty()){
    if(toDo.top().isEmpty()){
      toDo.pop();
      if(!toDo.isEmpty()){
        TermList ts = done.pop();
        unsigned s1 = doneSorts.pop();
        done.top() = apply(done.top(), doneSorts.top(), ts, s1);
        doneSorts.top() = range(doneSorts.top());
        /*cout << "\nDONE:" << endl;
        for(int i = done.size()-1; i >=0; i--){
          cout << done[i].toString() + " of sort " + env.sorts->sortName(doneSorts[i]) << endl;
        }*/
      }
    } else {
      HOTerm_ptr ht2 = toDo.top().pop();
      if(ht2->args.isEmpty()){
        done.top() = apply(done.top(), doneSorts.top(), ht2->head, ht2->headsort);
        doneSorts.top() = range(doneSorts.top());
      } else {
        done.push(ht2->head);
        doneSorts.push(ht2->headsort);
        //cout << "\nPushing head " + ht2->head.toString() + " with sort " + env.sorts->sortName(ht2->headsort) << endl;
        Stack<HOTerm_ptr> hts;
        toDo.push(hts);
        for(int i = ht2->args.size() - 1; i >=0; i--){
          //cout << "Pushing arg " + ht2->args[i]->toString(false, true) + " with sort " + env.sorts->sortName(ht2->args[i]->srt) << endl;
          toDo.top().push(ht2->args[i]);
        }
      }
    }
  }
  ASS(done.size() ==1);
  
  #if VDEBUG
    //cout << "The result is " + done.top().toString() << endl;
  #endif  
  return done.pop();
}

HOSortHelper::HOTerm_ptr HOSortHelper::deappify(TermList ts, int index, int sort){
  CALL("HOSortHelper::deappify");
  
  #if VDEBUG
    //cout << "deappifying " + ts.toString() << endl;
  #endif
  
  Stack<TermList> toDo;
  Stack<unsigned> toDoSorts;
  Stack<HOTerm_ptr> done;
  Stack<unsigned> argnums;

  if(ts.isVar()){
    if(sort > -1){
      return HOTerm_ptr(new HOTerm(ts, sort, index)); 
    } else {
      return HOTerm_ptr(new HOTerm(ts, 0, index));      
    }
  }

  toDo.push(ts);
  toDoSorts.push(SortHelper::getResultSort(ts.term()));

  while(!toDo.isEmpty()){
    TermList curr = toDo.pop();
    unsigned sort = toDoSorts.pop();

    if(curr.isVar() || (isConstant(curr) && !done.isEmpty())){
      done.top()->addArg(HOTerm_ptr(new HOTerm(curr, sort, index)));
      while(done.top()->args.size() == argnums.top()){
        argnums.pop();
        if(argnums.isEmpty()){ break; }
        HOTerm_ptr arg = done.pop();
        done.top()->addArg(arg);
      }
    } else if (isConstant(curr)){
      done.push(HOTerm_ptr(new HOTerm(curr, sort, index)));
    } else {
      unsigned headsort = sort;
      unsigned argnum = 0;
      Signature::Symbol* sym = env.signature->getFunction(curr.term()->functor());
      while(sym->hOLAPP()){
        argnum++;
        toDo.push(*(curr.term()->nthArgument(1)));
        toDoSorts.push(SortHelper::getArgSort(curr.term(), 1));
        headsort = SortHelper::getArgSort(curr.term(), 0);
        curr = *(curr.term()->nthArgument(0));
        if(curr.isVar()){ break; }
        sym = env.signature->getFunction(curr.term()->functor());
      }
      //constant
      done.push(HOTerm_ptr(new HOTerm(curr, headsort, index)));
      argnums.push(argnum);
    }
  }
  ASS(done.size());
  ASS(argnums.isEmpty());

  #if VDEBUG
    //cout << "The result is " + done.top()->toString(false, true) << endl;
    //ASSERTION_VIOLATION;
  #endif
  return done.pop();
}

/** view comment in .hpp file */
bool HOSortHelper::equal(const HOTerm_ptr hterm1, const HOTerm_ptr hterm2, bool useIndices)
{
  CALL("HOSortHelper::HOTerm::equal");
  
  Stack<HOTerm_ptr> toDo;

  toDo.push(hterm1);
  toDo.push(hterm2);
  
  while(!toDo.isEmpty()){
    HOTerm_ptr ht1 = toDo.pop();
    HOTerm_ptr ht2 = toDo.pop();
    if(ht1->varHead() && ht2->varHead()){
      if(useIndices && (ht1->headInd != ht2->headInd)){
        return false;
      } 
      if(ht1->head.var() != ht2->head.var()){
        return false;
      }
    } else if(ht1->head.isTerm() && ht2->head.isTerm()){
      if(ht1->head.term()->functor() != ht2->head.term()->functor()){
        return false;
      }
    } else {
      return false;
    }
    if(ht1->argnum() != ht2->argnum()){ return false; }
    for(unsigned i = 0; i < ht1->argnum(); i++){
      toDo.push(ht1->ntharg(i));
      toDo.push(ht2->ntharg(i));
    }
  }

  return true;
}

TermList HOSortHelper::getCombTerm(SS::HOLConstant cons, unsigned sort){
  CALL("HOSortHelper::getCombTerm");

  bool added;
  vstring name;
  switch(cons){
    case SS::I_COMB:
      name = "iCOMB";
      break;
    case SS::K_COMB:
      name = "kCOMB";
      break;
    case SS::B_COMB:
      name = "bCOMB";
      break;
    case SS::C_COMB:
      name = "cCOMB";
      break;
    case SS::S_COMB:
      name = "sCOMB";
      break;
    default:
      ASSERTION_VIOLATION;
  }

  unsigned fun = env.signature->addFunction(name + "_" +  Lib::Int::toString(sort),0,added);
  if(added){//first time constant added. Set type
      Signature::Symbol* symbol = env.signature->getFunction(fun);  
      symbol->setType(OperatorType::getConstantsType(sort));
      symbol->setHOLConstant(cons);   
  }
  return TermList(Term::createConstant(fun));
}

unsigned HOSortHelper::arity(unsigned sort){
  CALL("HOSortHelper::arity"); 
  
  if(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST))
  {
    return env.sorts->getFuncSort(sort)->arity();
  }
  return 0;
}

unsigned HOSortHelper::outputSort(unsigned sort){
  CALL("HOSortHelper::outputSort"); 
  
  while(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST))
  {
    sort = range(sort);
  }
  return sort; 
}

/** Given a functional sort, returns its range */
unsigned HOSortHelper::range(unsigned sort){
  CALL("HOSortHelper::range"); 
  
  ASS(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST));
  
  unsigned range = env.sorts->getFuncSort(sort)->getRangeSort();
  return range;  
}

/** Given a functional sort, returns its domain */
unsigned HOSortHelper::domain(unsigned sort){
  CALL("HOSortHelper::domain");  

  ASS(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST));
  
  unsigned dom = env.sorts->getFuncSort(sort)->getDomainSort();
  return dom;
}

unsigned HOSortHelper::getHigherOrderSort(const Stack<unsigned>& argsSorts, unsigned range)
{
  CALL("HOSortHelper::getHigherOrderSort");
  
  unsigned res = range;

  for(unsigned i = 0; i < argsSorts.size(); i++){
    res = env.sorts->addFunctionSort(argsSorts[i], res);
  }
  return res;

}

Term* HOSortHelper::createAppifiedTerm(TermList head, unsigned headsort,
                                       const Stack<unsigned>& argSorts,
                                       const Stack<TermList>& args){
  CALL("HOSortHelper::createAppifiedTerm");

  ASS(argSorts.size() == args.size());

  TermList res = head;
  unsigned sort = headsort;

  for(int i = args.size() - 1; i >= 0; i--){
    res = apply(res, sort, args[i], argSorts[i]);
    sort = range(sort);
  }

  return res.isTerm() ? res.term() : 0; 
}
