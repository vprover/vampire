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
#include "Lib/Environment.hpp"

#include "ApplicativeHelper.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2, TermList arg3, TermList arg4)
{
  TermList t1 = createAppTerm3(sort, arg1, arg2, arg3);
  return createAppTerm(SortHelper::getResultSort(t1.term()), t1, arg4);
}

TermList ApplicativeHelper::createAppTerm3(TermList sort, TermList arg1, TermList arg2, TermList arg3)
{
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  TermList s3 = getNthArg(s2, 1);
  TermList s4 = getResultApplieadToNArgs(s2, 1);
  return createAppTerm(s3, s4, createAppTerm(s1, s2, arg1, arg2), arg3);
}

TermList ApplicativeHelper::createAppTerm(TermList sort, TermList arg1, TermList arg2)
{
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  return createAppTerm(s1, s2, arg1, arg2);
}

TermList ApplicativeHelper::createAppTerm(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared)
{
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


/** indexed from 1 */
TermList ApplicativeHelper::getResultApplieadToNArgs(TermList arrowSort, unsigned argNum)
{
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
  while(sort.isArrowSort()){
    sort = *sort.term()->nthArgument(1);
  }
  return sort;
}

unsigned ApplicativeHelper::getArity(TermList sort)
{
  unsigned arity = 0;
  while(sort.isArrowSort()){
    sort = *sort.term()->nthArgument(1);
    arity++; 
  }
  return arity;
}

void ApplicativeHelper::getHeadAndAllArgs(TermList term, TermList& head, TermStack& args)
{
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
  if(!args.isEmpty()){ args.reset(); }

  while(term.isApplication()){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
  }
  head = term;

}


void ApplicativeHelper::getHeadAndArgs(Term* term, TermList& head, TermStack& args)
{
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
  TermList trm = TermList(t);
  while(t->isApplication()){
    trm = *t->nthArgument(2);
    if(!trm.isTerm() || trm.term()->isSpecial()){ break; }
    t = trm.term(); 
  }
  return trm;
}

Proxy ApplicativeHelper::getProxy(const TermList t)
{
  if(t.isVar()){
    return Proxy::NOT_PROXY;
  }
  return env.signature->getFunction(t.term()->functor())->proxy();
}

bool ApplicativeHelper::isBool(TermList t){
  return isTrue(t) || isFalse(t);
}

bool ApplicativeHelper::isTrue(TermList term){
  return term.isTerm() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

bool ApplicativeHelper::isFalse(TermList term){
  return term.isTerm() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

bool ApplicativeHelper::isSafe(TermStack& args)
{
  for(unsigned i = 0; i < args.size(); i++){
    TermList ithArg = args[i];
    /*if(ithArg.isVar() || !ithArg.term()->ground()){
      return false;
    }*/
    TermList head = getHead(ithArg);
    if (head.isVar()) {
      return false;
    }
  }
  return true;
}
