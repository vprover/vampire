/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/SmartPtr.hpp"

#include "ApplicativeHelper.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

TermList BetaReducer::transformSubterm(TermList t)
{
  CALL("BetaReducer::transformSubterm");

  if(!t.isApplication()) return t;
  t = ApplicativeHelper::betaReduce(t);
  t = BetaReducer().transform(t);
  return t;
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2, TermList arg3, TermList arg4)
{
  CALL("ApplicativeHelper::createAppTerm/3");

  TermList t1 = createAppTerm3(sort, arg1, arg2, arg3);
  return createAppTerm(SortHelper::getResultSort(t1.term()), t1, arg4);
}

TermList ApplicativeHelper::createAppTerm3(TermList sort, TermList arg1, TermList arg2, TermList arg3)
{
  CALL("ApplicativeHelper::createAppTerm3");
  
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  TermList s3 = getNthArg(s2, 1);
  TermList s4 = getResultApplieadToNArgs(s2, 1);
  return createAppTerm(s3, s4, createAppTerm(s1, s2, arg1, arg2), arg3);
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2)
{
  CALL("ApplicativeHelper::createAppTerm/2");
  
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  return createAppTerm(s1, s2, arg1, arg2);
}

TermList ApplicativeHelper::createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared)
{
  CALL("ApplicativeHelper::createAppTerm/1");
 
  static TermStack args;
  args.reset();
  args.push(s1);
  args.push(s2);
  args.push(arg1);
  args.push(arg2);
  unsigned app = env.signature->getApp();
  if(shared){
    return TermList(Term::create(app, 4, args.begin()));
  }
  return TermList(Term::createNonShared(app, 4, args.begin()));    
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList head, TermStack& terms)
{
  CALL("ApplicativeHelper::createAppTerm/4");
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort);

  TermList res = head;
  TermList s1, s2;
  
  for(int i = terms.size() - 1; i >= 0; i--){
    s1 = getNthArg(sort, 1);
    s2 = getResultApplieadToNArgs(sort, 1);
    res = createAppTerm(s1, s2, res, terms[i]);
    sort = s2;
  }
  return res; 

}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList head, TermList* args, unsigned arity, bool shared)
{
  CALL("ApplicativeHelper::createAppTerm/5");
  ASS_REP(head.isVar() || SortHelper::getResultSort(head.term()) == sort, sort.toString() );

  TermList res = head;
  TermList s1, s2;

  for(unsigned i = 0; i < arity; i++){
    s1 = getNthArg(sort, 1);
    s2 = getResultApplieadToNArgs(sort, 1);
    res = createAppTerm(s1, s2, res, args[i], shared);
    sort = s2;
  }
  return res; 
}  

TermList ApplicativeHelper::createLambdaTerm(TermList varSort, TermList termSort, TermList term)
{
  CALL("ApplicativeHelper::createLambdaTerm");

  static TermStack args;
  args.reset();
  args.push(varSort);
  args.push(termSort);
  args.push(term);
  unsigned lam = env.signature->getLam();
  return TermList(Term::create(lam, 3, args.begin()));
} 


TermList ApplicativeHelper::getDeBruijnIndex(int index, TermList sort)
{
  CALL("ApplicativeHelper::createDBIndex");
     
  bool added;
  unsigned fun = env.signature->addDeBruijnIndex(index, sort, added); 
  if(added){
    env.signature->getFunction(fun)->setType(OperatorType::getConstantsType(sort));
  }
  return TermList(Term::createConstant(fun));
}

/** indexed from 1 */
TermList ApplicativeHelper::getResultApplieadToNArgs(TermList arrowSort, unsigned argNum)
{
  CALL("ApplicativeHelper::getResultApplieadToNArgs");
  
  while(argNum > 0){
    ASS(arrowSort.isArrowSort());
    arrowSort = *arrowSort.term()->nthArgument(1);
    argNum--;
  }
  return arrowSort;
}


/** indexed from 1 */
TermList ApplicativeHelper::getNthArg(TermList arrowSort, unsigned argNum)
{
  CALL("ApplicativeHelper::getNthArg");
  ASS(argNum > 0);

  TermList res;
  while(argNum >=1){
    ASS(arrowSort.isArrowSort());
    res = *arrowSort.term()->nthArgument(0);
    arrowSort = *arrowSort.term()->nthArgument(1);
    argNum--;
  }
  return res;
}

TermList ApplicativeHelper::getResultSort(TermList sort)
{
  CALL("ApplicativeHelper::getResultSort");

  while(sort.isArrowSort()){
    sort = *sort.term()->nthArgument(1);
  }
  return sort;
}

unsigned ApplicativeHelper::getArity(TermList sort)
{
  CALL("ApplicativeHelper::getArity");

  unsigned arity = 0;
  while(sort.isArrowSort()){
    sort = *sort.term()->nthArgument(1);
    arity++; 
  }
  return arity;
}

void ApplicativeHelper::getHeadAndAllArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndAllArgs");

  while(term.isApplication()){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
  }
  head = term;  
  if(term.isTerm()){
    unsigned arity = term.term()->arity();
    for(int i = arity-1; i >= 0; i--){
      args.push(*term.term()->nthArgument(i));
    }
  }
} 

void ApplicativeHelper::getHeadSortAndArgs(TermList term, TermList& head, 
                                           TermList& headSort, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadSortAndArgs");

  if(!args.isEmpty()){ args.reset(); }

  if(!term.isTerm()){
    head = term;
    return;
  }

  while(term.isApplication()){
    Term* t = term.term();   
    args.push(*t->nthArgument(3)); 
    term = *t->nthArgument(2);
    if(!term.isApplication()){
      headSort = AtomicSort::arrowSort(*t->nthArgument(0), *t->nthArgument(1));
      break;   
    } 
  }
  head = term;
  
}


void ApplicativeHelper::getHeadAndArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs");

  if(!args.isEmpty()){ args.reset(); }

  while(term.isApplication()){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
  }
  head = term;

}


void ApplicativeHelper::getHeadAndArgs(Term* term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs/2");

  if(!args.isEmpty()){ args.reset(); }

  head = TermList(term);

  while(term->isApplication()){
    args.push(*term->nthArgument(3)); 
    head = *term->nthArgument(2);
    if(head.isTerm()){ 
      term = head.term();
    } else { break; }
  }

}

void ApplicativeHelper::getHeadAndArgs(const Term* term, TermList& head, Deque<TermList>& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs/3");

  ASS(term->isApplication());

  if(!args.isEmpty()){ args.reset(); }

  while(term->isApplication()){
    args.push_front(*term->nthArgument(3)); 
    head = *term->nthArgument(2);
    if(head.isTerm()){ 
      term = head.term();
    } else {  break; }
  }  
}


TermList ApplicativeHelper::getHead(TermList t)
{
  CALL("ApplicativeHelper::getHead(TermList)");
  
  if(!t.isTerm()){
    return t; 
  }

  while(t.isApplication()){
    t = *t.term()->nthArgument(2);
    if(!t.isTerm() || t.term()->isSpecial()){ break; } 
  }
  return t;
}

TermList ApplicativeHelper::getHead(Term* t)
{
  CALL("ApplicativeHelper::getHead(Term*)");
  
  TermList trm = TermList(t);
  while(t->isApplication()){
    trm = *t->nthArgument(2);
    if(!trm.isTerm() || trm.term()->isSpecial()){ break; }
    t = trm.term(); 
  }
  return trm;
}

Signature::Proxy ApplicativeHelper::getProxy(const TermList t)
{
  CALL("ApplicativeHelper::getProxy");
  if(t.isVar()){
    return Signature::NOT_PROXY;
  }
  return env.signature->getFunction(t.term()->functor())->proxy();
}

bool ApplicativeHelper::isBool(TermList t){
  CALL("ApplicativeHelper::isBool");
  return isTrue(t) || isFalse(t);
}

bool ApplicativeHelper::isTrue(TermList term){
  CALL("ApplicativeHelper::isTrue");
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

bool ApplicativeHelper::isFalse(TermList term){
  CALL("ApplicativeHelper::isFalse");
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

TermList ApplicativeHelper::betaReduce(TermList redex){
  CALL("ApplicativeHelper::betaReduce");

  ASS(redex.isApplication());
  TermList t1 = *redex.term()->nthArgument(2);
  TermList t2 = *redex.term()->nthArgument(3);
  ASS(t1.isLambdaTerm());

    Signature::Symbol* sym;
  
  unsigned replace = 0;
  Stack<TermList*> toDo;
  Stack<Term*> terms;
  Stack<bool> modified;
  Stack<TermList> args;

  modified.push(false);
  toDo.push(t1.term()->args());

  for (;;) {

    TermList* tt=toDo.pop();
    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();
      if(orig->isLambdaTerm()){ replace--; }
      
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();

    if(t->isLambdaTerm()){ replace++; }

    int index = t->deBruijnIndex();
    if(index > -1){
      if((unsigned)index == replace){
        //replace index with appropriately lifted term
        TermList liftedTerm = lift(t2, replace);
        args.push(liftedTerm);
        modified.setTop(true);
        continue;
      }
      if((unsigned)index > replace){
        //free index, decrement by one, as now surrounded by one less lambda.
        args.push(getDeBruijnIndex(index - 1, SortHelper::getResultSort(t)));
        modified.setTop(true);        
        continue;
      }
    }      
    
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(), 1);

  //original abstracted term being a lambda term must have
  //arity 1. Currently, there is a problem if the abstractedTerm is of 
  //the form lam(X). In that case we want to return X, but X is not 
  //a term.   
  return args.top();
}
