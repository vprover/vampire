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
 * @file CombinatorDemodISE.cpp
 * Implements class CombinatorDemodISE.
 */

#include "Lib/Random.hpp"
#include "Lib/Environment.hpp"
#include "Lib/DArray.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SKIKBO.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Statistics.hpp"
#include "CombinatorDemodISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

typedef ApplicativeHelper AH; 

Clause* CombinatorDemodISE::simplify(Clause* c)
{
  CALL("CombinatorDemodISE::simplify");

  Literal* newLit;
  LiteralStack litStack;
  bool modified = false;

 // cout << "into CombinatorDemodISE " + c->toString() << endl;

  unsigned length = 0;
  unsigned length0;
  unsigned length1;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    ASS(lit->isEquality());
    TermList t0 = *lit->nthArgument(0);
    TermList t1 = *lit->nthArgument(1);
    
    length0 = 0;
    length1 = 0;

    TermList t0r = t0.isVar() ? t0 : reduce(t0, length0);
    TermList t1r = t1.isVar() ? t1 : reduce(t1, length1);      
    
    length = length + length0 + length1;

    if((t0r != t0) || (t1r != t1)){
      modified = true;
      newLit = Literal::createEquality(lit->polarity(), TermList(t0r), TermList(t1r), SortHelper::getResultSort(t0.term()));
      litStack.push(newLit);
    } else {
      litStack.push(lit);
    }  
  }

  if(!modified){
    return c;
  }

  Inference inf = SimplifyingInference1(InferenceRule::COMBINATOR_DEMOD, c);
  inf.increaseReductions(length);
  Clause* newC = Clause::fromStack(litStack, inf);
  /*if(c->number() == 1620){
    cout << "out of CombinatorDemodISE " + newC->toString() << endl;
  }*/
  //if(!newC){ cout << "RETURNING NULL CLAUSE" << endl; }
  return newC;
}

TermList CombinatorDemodISE::reduce(TermList t, unsigned& length)
{
  CALL("CombinatorDemodISE::reduce");
  
  typedef SmartPtr<ApplicativeArgsIt> ArgsIt_ptr;

  ASS(!t.isVar());
    
  static Stack<Term*> terms(8);
  static Stack<AH::HigherOrderTermInfo> infos(8);
  static Stack<bool> modified(8);
  static Stack<ArgsIt_ptr> argIts(8);
  static TermStack args;

  ASS(argIts.isEmpty());
  ASS(terms.isEmpty());
  ASS(infos.isEmpty());
  modified.reset();
  args.reset();

  headNormalForm(t);
  modified.push(false);
  argIts.push(ArgsIt_ptr(new ApplicativeArgsIt(t, false)));
  ArgsIt_ptr argsIt = argIts.top();
  infos.push(AH::HigherOrderTermInfo(argsIt->head(), argsIt->headSort(), argsIt->argNum()));

  for (;;) {
    if (!argIts.top()->hasNext()) {
      argIts.pop();
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(argIts.isEmpty());
        break;
      }
      Term* orig = terms.pop();
      AH::HigherOrderTermInfo hoti=infos.pop();
      if (!modified.pop()) {
        args.truncate(args.length() - hoti.argNum);
        args.push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (hoti.argNum - 1);
      args.truncate(args.length() - hoti.argNum);

      TermList trm = AH::createAppTerm(hoti.headSort, hoti.head, argLst, hoti.argNum);
      args.push(trm);
      modified.setTop(true);
      continue;
    }

    TermList tl= argIts.top()->next();
    bool reduced = headNormalForm(tl);
    if(reduced){
      length++;
      modified.setTop(true);
    }
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    terms.push(t);
    modified.push(false);
    argIts.push(ArgsIt_ptr(new ApplicativeArgsIt(tl, false)));
    argsIt = argIts.top();
    infos.push(AH::HigherOrderTermInfo(argsIt->head(), argsIt->headSort(), argsIt->argNum()));
  }
  ASS(argIts.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(infos.length(),1);
  AH::HigherOrderTermInfo hoti=infos.pop();
  ASS_EQ(args.length(),hoti.argNum);

  if (!modified.pop()) {
    return t;
  }

  TermList* argLst=&args.top() - (hoti.argNum-1);
  ASS(!t.term()->isLiteral());
  return AH::createAppTerm(hoti.headSort, hoti.head, argLst, hoti.argNum);;
}

bool CombinatorDemodISE::headNormalForm(TermList& t)
{
  CALL("CombinatorDemodISE::headNormalForm");

  static TermStack args;
  TermList head;
  
  bool modified = false;
  
  for(;;){
    AH::getHeadAndArgs(t, head, args);
    if(AH::isComb(head) && !AH::isUnderApplied(head, args.size())){
      modified = true;
      t = SKIKBO::reduce(args, head);
    } else {
      break; 
    }
  }
  return modified;
}



