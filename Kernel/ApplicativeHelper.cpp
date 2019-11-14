
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/SmartPtr.hpp"

#include "ApplicativeHelper.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

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

  for(int i = 0; i < arity; i++){
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
  CALL("ApplicativeHelper::getResultApplieadToNArgs");
  
  while(argNum > 0){
    ASS(arrowSort.isTerm() && env.signature->getFunction(arrowSort.term()->functor())->arrow());
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
    ASS(arrowSort.isTerm() && env.signature->getFunction(arrowSort.term()->functor())->arrow());
    res = *arrowSort.term()->nthArgument(0);
    arrowSort = *arrowSort.term()->nthArgument(1);
    argNum--;
  }
  return res;
}

TermList ApplicativeHelper::getResultSort(TermList sort)
{
  CALL("ApplicativeHelper::getResultSort");

  while(sort.isTerm() && env.signature->getFunction(sort.term()->functor())->arrow()){
    sort = *sort.term()->nthArgument(1);
  }
  return sort;
}

void ApplicativeHelper::getHeadAndAllArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndAllArgs");

  if(!term.isTerm()){
    head = term;
    return;
  }

  while(isApp(term.term())){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
    if(!term.isTerm()){ break; } 
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

  if(!term.isTerm()){
    head = term;
    return;
  }

  while(isApp(term.term())){
    Term* t = term.term();   
    args.push(*t->nthArgument(3)); 
    term = *t->nthArgument(2);
    if(!term.isTerm() || !isApp(term.term())){
      headSort = Term::arrowSort(*t->nthArgument(0), *t->nthArgument(1));
      break;   
    } 
  }
  head = term;
  
}


void ApplicativeHelper::getHeadAndArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs");

  if(!term.isTerm()){
    head = term;
    return;
  }

  while(isApp(term.term())){
    args.push(*term.term()->nthArgument(3)); 
    term = *term.term()->nthArgument(2);
    if(!term.isTerm()){ break; } 
  }
  head = term;

}


void ApplicativeHelper::getHeadAndArgs(Term* term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs/2");

  head = TermList(term);

  while(isApp(term)){
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

  ASS(isApp(term));

  while(isApp(term)){
    args.push_front(*term->nthArgument(3)); 
    head = *term->nthArgument(2);
    if(head.isTerm()){ 
      term = head.term();
    } else {  break; }
  }  
}



TermList ApplicativeHelper::getHead(TermList t)
{
  CALL ("getHead");
  
  if(!t.isTerm()){
    return t; 
  }

  while(env.signature->getFunction(t.term()->functor())->app()){
    t = *t.term()->nthArgument(2);
    if(!t.isTerm()){ break; } 
  }
  return t;
}

bool ApplicativeHelper::isComb(TermList head)
{
  CALL("ApplicativeHelper::isComb");
  if(head.isVar()){ return false; }
  return env.signature->getFunction(head.term()->functor())->combinator() != Signature::NOT_COMB;
}

Signature::Combinator ApplicativeHelper::getComb (TermList head) 
{
  CALL("ApplicativeHelper::getComb");
  return env.signature->getFunction(head.term()->functor())->combinator();
}

bool ApplicativeHelper::isApp(const Term* t)
{
  CALL("ApplicativeHelper::isApp(Term*)");
  return env.signature->getFunction(t->functor())->app(); 
}

bool ApplicativeHelper::isApp(const TermList* tl)
{
  CALL("ApplicativeHelper::isApp(TermList*)");
  if(tl->isTerm()){ return isApp(tl->term()); }
  return false;
}

bool ApplicativeHelper::isArrowType(const Term* t)
{
  CALL("ApplicativeHelper::isApp(Term*)");
  return env.signature->getFunction(t->functor())->arrow(); 
}

bool ApplicativeHelper::isType(const Term* t)
{
  CALL("ApplicativeHelper::isType(Term*)");
  return env.signature->getFunction(t->functor())->super() ||
         SortHelper::getResultSort(t) == Term::superSort();
}

bool ApplicativeHelper::isUnderApplied(TermList head, unsigned argNum){
  CALL("ApplicativeHelper::isPartiallyAppliedComb");

  ASS(isComb(head));
  Signature::Combinator c = getComb(head);
  return ((c == Signature::I_COMB && argNum < 1) ||
          (c == Signature::K_COMB && argNum < 2) ||
          (c == Signature::B_COMB && argNum < 3) ||
          (c == Signature::C_COMB && argNum < 3) ||
          (c == Signature::S_COMB && argNum < 3));
}

bool ApplicativeHelper::isExactApplied(TermList head, unsigned argNum){
  CALL("ApplicativeHelper::isExactApplied");

  ASS(isComb(head));
  Signature::Combinator c = getComb(head);
  return ((c == Signature::I_COMB && argNum == 1) ||
          (c == Signature::K_COMB && argNum == 2) ||
          (c == Signature::B_COMB && argNum == 3) ||
          (c == Signature::C_COMB && argNum == 3) ||
          (c == Signature::S_COMB && argNum == 3));

}


bool ApplicativeHelper::isOverApplied(TermList head, unsigned argNum){
  CALL("ApplicativeHelper::isOverApplied");

  ASS(isComb(head));
  Signature::Combinator c = getComb(head);
  return ((c == Signature::I_COMB && argNum > 1) ||
          (c == Signature::K_COMB && argNum > 2) ||
          (c == Signature::B_COMB && argNum > 3) ||
          (c == Signature::C_COMB && argNum > 3) ||
          (c == Signature::S_COMB && argNum > 3));

}



bool ApplicativeHelper::isSafe(TermStack& args)
{
  CALL("ApplicativeHelper::isSafe");

  for(unsigned i = 0; i < args.size(); i++){
    TermList ithArg = args[i];
    /*if(ithArg.isVar() || !ithArg.term()->ground()){
      return false;
    }*/
    TermList head = getHead(ithArg);
    if(isComb(head) || head.isVar()){
      return false;
    }
  }
  return true;
}

TermList ApplicativeHelper::replaceFunctionalSubterms(Term* term, FuncSubtermMap* fsm)
{
  CALL("TermSubstitutionTree::replaceFunctionalSubterms");
  
  typedef SmartPtr<ApplicativeArgsIt> ArgsIt_ptr;
  typedef ApplicativeHelper AH;
    
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

  modified.push(false);
  argIts.push(ArgsIt_ptr(new ApplicativeArgsIt(TermList(term), false)));
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

      TermList trm = AH::createAppTerm(hoti.headSort, hoti.head, argLst, hoti.argNum, false);
      args.push(trm);
      modified.setTop(true);
      continue;
    }

    TermList tl= argIts.top()->next();
    if(tl.isTerm()){
      TermList sort = SortHelper::getResultSort(tl.term());
      if(sort.isVar() || ApplicativeHelper::isArrowType(sort.term())){
        tl = getVSpecVar(tl.term(), fsm);
        modified.setTop(true);
      }      
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
    return TermList(term);
  }

  TermList* argLst=&args.top() - (hoti.argNum-1);
  ASS(!term->isLiteral());
  return AH::createAppTerm(hoti.headSort, hoti.head, argLst, hoti.argNum, false);
}