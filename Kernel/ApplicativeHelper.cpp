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
#include "Kernel/EqHelper.hpp"

#include "ApplicativeHelper.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

#if VHOL

TermList BetaNormaliser::normalise(TermList t)
{
  CALL("BetaNormaliser::normalise");

  // term transformer does not work at the top level...
  t = transformSubterm(t);
  return transform(t);
}

TermList BetaNormaliser::transformSubterm(TermList t)
{
  CALL("BetaNormaliser::transformSubterm");

  while(t.isRedex()){
    t = RedexReducer().reduce(t);
  }

  return t;
}

bool BetaNormaliser::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("BetaNormaliser::exploreSubterms");

  if(newTerm.term()->hasRedex()) return true;
  return false;
}

TermList EtaNormaliser::normalise(TermList t)
{
  CALL("EtaNormaliser::normalise");

  _ignoring = false;
  t = transformSubterm(t);
  return transform(t);
}

TermList EtaNormaliser::transformSubterm(TermList t)
{
  CALL("EtaNormaliser::transformSubterm");

  if(_ignoring && t != _awaiting) return t;
  if(_ignoring && t == _awaiting) _ignoring = false;

  TermList body = t;
  unsigned l = 0; // number of lambda binders
  while(body.isLambdaTerm()){
    l++;
    body = body.lambdaBody();
  }
  if(!l) return t; //not a lambda term, cannot eta reduce
  
  unsigned n = 0; // number of De bruijn indices at end of term 
  TermList newBody = body;
  while(body.isApplication()){
    auto dbIndex = body.rhs().deBruijnIndex();
    if(!dbIndex.isSome() || dbIndex.unwrap() != n){
      break;
    }
    body = body.lhs();
    n++;
  }

  TermShifter ts;
  ts.shift(body, 0);
  auto mfi = ts.minFreeIndex();
  unsigned j = mfi.isSome() ? mfi.unwrap() : UINT_MAX; // j is minimum free index
  unsigned k = std::min(l, std::min(n, j));

  if(!k){
    _ignoring = true;
    _awaiting = newBody;
    return t;
  }

  for(unsigned i = 0; i < k; i++){
    newBody = newBody.lhs();
  }
  newBody = TermShifter().shift(newBody, 0 - k);

  body = t;
  for(unsigned i = 0; i < l - k; i++){
    body = body.lambdaBody();
  }

  // TermTransform doesn't work at top level...
  if(body == t){
    return newBody;
  }

  _ignoring = true;
  _awaiting = newBody;

  return SubtermReplacer(body, newBody).transform(t);
}

bool EtaNormaliser::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("EtaNormaliser::exploreSubterms");

  while(newTerm.isLambdaTerm()){
    newTerm = newTerm.lambdaBody();
  }
  if(newTerm.isVar() || !newTerm.term()->hasLambda()) return false;
  return true;
}

TermList RedexReducer::reduce(TermList redex)
{
  CALL("RedexReducer::reduce");
  ASS(redex.isRedex());

  _replace = 0;
  TermList t1 = redex.lhs().lambdaBody();
  _t2 = redex.rhs();

  if(t1.isTerm()) onTermEntry(t1.term());
  TermList transformed = transformSubterm(t1);

  if(transformed != t1) return transformed;  
  return transform(t1);
}

TermList RedexReducer::transformSubterm(TermList t)
{
  CALL("RedexReducer::transformSubterm");

  if(t.deBruijnIndex().isSome()){
    unsigned index = t.deBruijnIndex().unwrap();
    if(index == _replace){
      // any free indices in _t2 need to be lifted by the number of extra lambdas 
      // that now surround them
      return TermShifter().shift(_t2, _replace); 
    }
    if(index > _replace){
      // free index. replace by index 1 less as now surrounded by one fewer lambdas
      TermList sort = SortHelper::getResultSort(t.term());
      return ApplicativeHelper::getDeBruijnIndex(index - 1, sort);
    }
  } 
  return t;
}

void RedexReducer::onTermEntry(Term* t)
{
  CALL("RedexReducer::onTermEntry");
   
  if(t->isLambdaTerm()) _replace++;
}

void RedexReducer::onTermExit(Term* t)
{
  CALL("RedexReducer::onTermExit");

  if(t->isLambdaTerm()) _replace--;
}

bool RedexReducer::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("RedexReducer::exploreSubterms");

  if(orig != newTerm) return false;
  if(newTerm.term()->hasDBIndex()) return true;
  return false;
}

TermList TermShifter::shift(TermList term, int shiftBy)
{
  CALL("TermShifter::shift");

  _cutOff = 0;
  _shiftBy = shiftBy;

  if(term.isTerm()) onTermEntry(term.term());  
  TermList transformed = transformSubterm(term);
  if(transformed != term) return transformed;    
  return transform(term);
}

TermList TermShifter::transformSubterm(TermList t)
{
  CALL("TermShifter::transformSubterm");

  if(t.deBruijnIndex().isSome()){
    unsigned index = t.deBruijnIndex().unwrap();
    if(index >= _cutOff){
      // free index. lift
      if(_shiftBy != 0){
        TermList sort = SortHelper::getResultSort(t.term());
        ASS(_shiftBy >= 0 || index >= std::abs(_shiftBy));
        return ApplicativeHelper::getDeBruijnIndex(index + _shiftBy, sort);
      } else {
        _minFreeIndex = (int)index;
      }
    }
  }
  return t;
} 

void TermShifter::onTermEntry(Term* t)
{
  CALL("TermShifter::onTermEntry");

  if(t->isLambdaTerm()) _cutOff++;
}

void TermShifter::onTermExit(Term* t)
{
  CALL("TermShifter::onTermExit");

  if(t->isLambdaTerm()) _cutOff--;
}

bool TermShifter::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("TermShifter::exploreSubterms");

  // already shifted, so must be DB index and won't have subterms anyway
  if(orig != newTerm) return false;
  if(newTerm.term()->hasDBIndex()) return true;
  return false;
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
  auto t = TermList(Term::createConstant(fun));
  return t;
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

TermList ApplicativeHelper::headSort(TermList app)
{
  CALL("ApplicativeHelper::getHeadSort");
  ASS(app.isApplication());

  return AtomicSort::arrowSort(*app.term()->nthArgument(0), *app.term()->nthArgument(1));
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

void ApplicativeHelper::getArgSorts(TermList t, TermStack& sorts)
{
  CALL("ApplicativeHelper::getArgSorts");
  ASS(t.isApplication());

  while(t.isApplication()){
    sorts.push(*t.term()->nthArgument(0));
    t = t.lhs();
  }
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


#endif
