
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

  if(t.isLambdaTerm()) return t;

  TermList head;
  TermStack args;
  ApplicativeHelper::getHeadAndArgs(t, head, args);

  while(ApplicativeHelper::canHeadReduce(head, args)){
    t = RedexReducer().reduce(head, args);
    if(t.isLambdaTerm()) break;
    ApplicativeHelper::getHeadAndArgs(t, head, args);    
  }
  
  return t;
}

bool BetaNormaliser::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("BetaNormaliser::exploreSubterms");

  if(newTerm.term()->hasRedex()) return true;
  return false;
}

TermList WHNFDeref::normalise(TermList t)
{
  CALL("WHNFDeref::normalise");

  // term transformer does not work at the top level...
  t = transformSubterm(t);
  return t.isLambdaTerm() ? transform(t) : t;
}

TermList WHNFDeref::transformSubterm(TermList t)
{
  CALL("WHNFDeref::transformSubterm");

  if(t.isLambdaTerm()) return t;

  TermList head;
  TermList sort;
  TermStack args;
  ApplicativeHelper::getHeadSortAndArgs(t, head, sort, args);
  TermList newHead = _sub->derefBound(head);
  newHead = SortDeref(_sub).deref(newHead);
 
  // if the head is a bound variable, then 
  // either it is bound to a lambda term creating a redex on dereferencing,
  // or it is not. In the case, it isn't we need to track
  // that the head has changed
  bool headDereffed = newHead != head;

  while(ApplicativeHelper::canHeadReduce(newHead, args)){
    headDereffed = false;
    t = RedexReducer().reduce(newHead, args);
    if(t.isLambdaTerm()) break;
    ApplicativeHelper::getHeadSortAndArgs(t, head, sort, args);    
    newHead = _sub->derefBound(head);
    newHead = SortDeref(_sub).deref(newHead);
    headDereffed = newHead != head;
  }
  
  if(!headDereffed){
    return t;
  } else if(!args.size()){
    return newHead;
  } else {
    return ApplicativeHelper::app(sort, newHead, args);
  }

}

bool WHNFDeref::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("WHNFDeref::exploreSubterms");

  return newTerm.isLambdaTerm();
}

TermList EtaNormaliser::normalise(TermList t)
{
  CALL("EtaNormaliser::normalise");

  using AH = ApplicativeHelper;

  if(t.isVar() || !t.term()->hasLambda()){
    return t;
  }

  if(t.isLambdaTerm()){
    TermStack lambdaSorts;
    TermList matrix;
    AH::getMatrixAndPrefSorts(t, matrix, lambdaSorts); 
    
    if(matrix.isVar()) return t; // ^^^^^^X can't eta reduce this
    
    TermList matrixSort = SortHelper::getResultSort(matrix.term());
    TermList reduced = normalise(matrix);
    if(reduced != matrix){
      t = AH::surroundWithLambdas(reduced, lambdaSorts, matrixSort, true);
    }
    
    return transformSubterm(t);
  }

  // t is not a lambda term

  TermList head;
  TermList headSort;
  TermStack args;
  TermStack argsModified;
  AH::getHeadSortAndArgs(t, head, headSort, args);

  bool changed = false;
  for(unsigned j = 0; j < args.size(); j++){
    argsModified.push(normalise(args[j]));
    changed = changed || (argsModified[j] != args[j]);
  }

  if(!changed) return t;
  TermList res = AH::app(headSort,head,argsModified);
  

  return res;
}

// uses algorithm for eta-reduction that can be found here:
// https://matryoshka-project.github.io/pubs/lambdae.pdf

TermList EtaNormaliser::transformSubterm(TermList t)
{
  CALL("EtaNormaliser::transformSubterm");

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

  TermList res = SubtermReplacer(body, newBody).transform(t);
  return res;
}

TermList RedexReducer::reduce(TermList head, TermStack& args)
{
  CALL("RedexReducer::reduce");
  ASS(AH::canHeadReduce(head, args));

  _replace = 0;
  TermList t1 = head.lambdaBody();
  TermList t1Sort = *head.term()->nthArgument(1);
  _t2 = args.pop();

  TermList transformed = transformSubterm(t1);

  if(transformed != t1) return AH::app(t1Sort, transformed, args);  
  return AH::app(t1Sort, transform(t1), args);
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
        int j = (int)(index - _cutOff);
        if(j < _minFreeIndex || _minFreeIndex == -1){
          _minFreeIndex = j;
        }
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

TermList SortDeref::deref(TermList term)
{
  CALL("SortDeref::deref");

  // assume term var here
  if(term.isVar() || !term.term()->hasSortVar()) return term;
  return transform(term);
}

TermList SortDeref::transformSubterm(TermList t)
{
  CALL("ortDeref::transformSubterm");

  if(t.isVar() && _positions.top() < _typeArities.top()){
    t = _sub->derefBound(t);
  }
  unsigned pos = _positions.pop();
  _positions.push(pos + 1);
  return t;
}

void SortDeref::onTermEntry(Term* t){
  CALL("SortDeref::onTermEntry");

  _typeArities.push(t->isSort() ? t->arity() : t->numTypeArguments());
  _positions.push(0);
}

void SortDeref::onTermExit(Term* t){
  CALL("ortDeref::onTermExit");

  _typeArities.pop();
  _positions.pop();
} 

bool SortDeref::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("SortDeref::exploreSubterms");

  ASS(newTerm.isTerm());

  return newTerm.term()->hasSortVar();
}

TermList ToPlaceholders::replace(TermList term)
{
  CALL("ToPlaceholders::replace");

  TermList transformed = transformSubterm(term);
  if(transformed != term) return transformed;    
  _topLevel = false;
  return transform(term);  
}

TermList ToPlaceholders::transformSubterm(TermList t)
{
  CALL("ToPlaceholders::transformSubterm");

  typedef ApplicativeHelper AH;

  if(_nextIsPrefix) return t;
  if(t.isVar()) return t;

  // Not expecting any unreduced redexes here
  ASS(!t.head().isLambdaTerm());

  auto sort = SortHelper::getResultSort(t.term());
  if(t.isLambdaTerm() ||  t.head().isVar()) return AH::placeholder(sort);

  if(_mode == Options::FunctionExtensionality::ABSTRACTION){
    if(sort.isArrowSort() || sort.isVar() || (sort.isBoolSort() && !_topLevel)){
      return AH::placeholder(sort);
    }
  }
  return t;
} 

void ToPlaceholders::onTermEntry(Term* t)
{
  CALL("ToPlaceholders::onTermEntry");

  if(t->isApplication()) _nextIsPrefix = true;
}

void ToPlaceholders::onTermExit(Term* t)
{
  CALL("ToPlaceholders::onTermExit");

  _nextIsPrefix = false;
}

TermList ApplicativeHelper::app2(TermList sort, TermList head, TermList arg1, TermList arg2)
{
  CALL("ApplicativeHelper::app2");
  
  return app(app(sort, head, arg1), arg2);
}

TermList ApplicativeHelper::app2(TermList head, TermList arg1, TermList arg2)
{ 
  CALL("ApplicativeHelper::app2");
  ASS(head.isTerm());
  
  TermList headSort = SortHelper::getResultSort(head.term());
  return app2(headSort, head, arg1, arg2);
}  

TermList ApplicativeHelper::app(TermList sort, TermList head, TermList arg)
{
  CALL("ApplicativeHelper::app");
  
  TermList s1 = getNthArg(sort, 1);
  TermList s2 = getResultApplieadToNArgs(sort, 1);
  return app(s1, s2, head, arg);
}

TermList ApplicativeHelper::app(TermList head, TermList arg)
{
  CALL("ApplicativeHelper::app/2");
  ASS(head.isTerm());

  return app(SortHelper::getResultSort(head.term()), head, arg);
}

TermList ApplicativeHelper::app(TermList s1, TermList s2, TermList arg1, TermList arg2, bool shared)
{
  CALL("ApplicativeHelper::app/3");

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

TermList ApplicativeHelper::app(TermList sort, TermList head, TermStack& terms)
{
  CALL("ApplicativeHelper::app/4");
  ASS(head.isVar() || SortHelper::getResultSort(head.term()) == sort);

  TermList res = head;
  TermList s1, s2;

  for(int i = terms.size() - 1; i >= 0; i--){
    s1 = getNthArg(sort, 1);
    s2 = getResultApplieadToNArgs(sort, 1);
    res = app(s1, s2, res, terms[i]);
    sort = s2;
  }
  return res; 

}

TermList ApplicativeHelper::app(TermList head, TermStack& terms)
{
  CALL("ApplicativeHelper::app/5");
  ASS(head.isTerm());

  TermList sort = SortHelper::getResultSort(head.term());
  return app(sort, head, terms); 
}

TermList ApplicativeHelper::lambda(TermList varSort, TermList termSort, TermList term)
{
  CALL("ApplicativeHelper::lambda");

  ASS(varSort.isVar()  || varSort.term()->isSort());
  ASS(termSort.isVar() || termSort.term()->isSort());

  static TermStack args;
  args.reset();
  args.push(varSort);
  args.push(termSort);
  args.push(term);
  unsigned lam = env.signature->getLam();
  return TermList(Term::create(lam, 3, args.begin()));
} 

TermList ApplicativeHelper::lambda(TermList varSort, TermList term)
{
  CALL("ApplicativeHelper::lambda/2");
  ASS(term.isTerm());
  
  TermList termSort = SortHelper::getResultSort(term.term());
  return lambda(varSort, termSort, term);
}

TermList ApplicativeHelper::matrix(TermList t)
{
  CALL("ApplicativeHelper::matrix");

  while(t.isLambdaTerm()){
    t = t.lambdaBody();
  }
  return t;
}


TermList ApplicativeHelper::getDeBruijnIndex(int index, TermList sort)
{
  CALL("ApplicativeHelper::createDBIndex");
     
  unsigned fun = env.signature->getDeBruijnIndex(index); 
  return TermList(Term::create1(fun, sort));
}

TermList ApplicativeHelper::placeholder(TermList sort)
{
  CALL("ApplicativeHelper::placeholder");

  unsigned fun = env.signature->getPlaceholder(); 
  return TermList(Term::create1(fun, sort));  
}

/** indexed from 1 */
TermList ApplicativeHelper::getResultApplieadToNArgs(TermList arrowSort, unsigned argNum)
{
  CALL("ApplicativeHelper::getResultApplieadToNArgs");
  
  while(argNum > 0){
    ASS(arrowSort.isArrowSort());
    arrowSort = arrowSort.result();
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
    res = arrowSort.domain();
    arrowSort = arrowSort.result();
    argNum--;
  }
  return res;
}

unsigned ApplicativeHelper::getArity(TermList sort)
{
  CALL("ApplicativeHelper::getArity");

  unsigned arity = 0;
  while(sort.isArrowSort()){
    sort = sort.result();
    arity++; 
  }
  return arity;
}

/*void ApplicativeHelper::getHeadAndAllArgs(TermList term, TermList& head, TermStack& args)
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
} */

void ApplicativeHelper::getHeadSortAndArgs(TermList term, TermList& head, 
                                           TermList& headSort, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadSortAndArgs");

  if(!args.isEmpty()){ args.reset(); }

  term = matrix(term);

  while(term.isApplication()){
    args.push(term.rhs()); 
    TermList t = term.lhs();
    if(!t.isApplication()){
      headSort = AtomicSort::arrowSort(term.nthArg(0), term.nthArg(1));
    } 
    term = t;
  }
  head = term;
}

void ApplicativeHelper::getHeadArgsAndArgSorts(TermList t, TermList& head, TermStack& args, TermStack& argSorts)
{
  CALL("ApplicativeHelper::getHeadArgsAndArgSorts");

  if(!args.isEmpty()){ args.reset(); }
  if(!argSorts.isEmpty()){ argSorts.reset(); }

  t = matrix(t);

  while(t.isApplication()){
    args.push(t.rhs()); 
    argSorts.push(rhsSort(t));
    t = t.lhs();
  }
  head = t;  
}

void ApplicativeHelper::getMatrixAndPrefSorts(TermList t, TermList& matrix, TermStack& sorts)
{
  CALL("ApplicativeHelper::getLambdaPrefSorts");
  
  while(t.isLambdaTerm()){
    sorts.push(*t.term()->nthArgument(0));
    t = t.lambdaBody();
  }
  matrix = t;
}

void ApplicativeHelper::getArgSorts(TermList t, TermStack& sorts)
{
  CALL("ApplicativeHelper::getArgSorts");

  while(t.isArrowSort()){
    sorts.push(t.domain());
    t = t.result();    
  }

  t = matrix(t);

  while(t.isApplication()){
    sorts.push(*t.term()->nthArgument(0));
    t = t.lhs();
  }
}


void ApplicativeHelper::getHeadAndArgs(TermList term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs");

  if(!args.isEmpty()){ args.reset(); }

  term = matrix(term);

  while(term.isApplication()){
    args.push(term.rhs()); 
    term = term.lhs();
  }
  head = term;
}

void ApplicativeHelper::getHeadAndArgs(Term* term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs/2");

  getHeadAndArgs(TermList(term), head, args);
}

void ApplicativeHelper::getHeadAndArgs(const Term* term, TermList& head, TermStack& args)
{
  CALL("ApplicativeHelper::getHeadAndArgs/5");

  getHeadAndArgs(const_cast<Term*>(term),head,args);
}

TermList ApplicativeHelper::lhsSort(TermList t)
{
  CALL("ApplicativeHelper::lhsSort");
  ASS(t.isApplication());

  TermList s1 = *t.term()->nthArgument(0);
  TermList s2 = *t.term()->nthArgument(1);
  return AtomicSort::arrowSort(s1,s2);
}   

TermList ApplicativeHelper::rhsSort(TermList t)
{
  CALL("ApplicativeHelper::rhsSort")
  ASS(t.isApplication());

  return *t.term()->nthArgument(0);
}   

Signature::Proxy ApplicativeHelper::getProxy(const TermList& t)
{
  CALL("ApplicativeHelper::getProxy");
  if(t.isVar()){
    return Signature::NOT_PROXY;
  }
  return env.signature->getFunction(t.term()->functor())->proxy();
}

void ApplicativeHelper::getAbstractionTerms(Literal* lit, TermStack& terms)
{
  CALL("ApplicativeHelper::getAbstractionTerms");

  ASS(lit->isEquality());

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  TermList eqSort = SortHelper::getEqualityArgumentSort(lit);


  auto dealWithArg = [&](TermList arg, TermList argSort, TermStack& terms){
    if(!arg.containsLooseIndex()){
      TermList db = getDeBruijnIndex(0,argSort);
      SubtermReplacer st(arg,db,true);
      TermList lhsReplaced = st.transform(lhs);
      TermList rhsReplaced = st.transform(rhs);
      TermList eq = app2(equality(eqSort), lhsReplaced, rhsReplaced);
      eq = lit->polarity() ? app(neg(),eq) : eq; // reverse the polarity of the literal
      terms.push(lambda(argSort,eq));
    }
  };

  TermList lhsHead, rhsHead;
  TermList lhsMatrix, rhsMatrix;
  static TermStack lhsArgs;
  static TermStack lhsArgSorts;
  static TermStack rhsArgs;
  static TermStack rhsArgSorts;


  getHeadArgsAndArgSorts(lhs, lhsHead, lhsArgs, lhsArgSorts);
  getHeadArgsAndArgSorts(rhs, rhsHead, rhsArgs, rhsArgSorts);
  if(lhsHead.isTerm() && lhsHead.deBruijnIndex().isNone() && lhsHead == rhsHead)
  {
    for(unsigned i = 0; i < lhsArgs.size(); i++){
      dealWithArg(lhsArgs[i], lhsArgSorts[i], terms);
    }

    for(unsigned i = 0; i < rhsArgs.size(); i++){
      dealWithArg(rhsArgs[i], rhsArgSorts[i], terms);
    }
  }
}

bool ApplicativeHelper::isBool(TermList t){
  CALL("ApplicativeHelper::isBool");
  return isTrue(t) || isFalse(t);
}

bool ApplicativeHelper::splittable(TermList t, bool topLevel){
  CALL("ApplicativeHelper::splittable1");

  if(t.isVar()) return true;

  ASS(!t.head().isLambdaTerm()); // assume t is in head normal form
  if(t.isLambdaTerm() ||  t.head().isVar()) return false;

  if(env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION){
    auto sort = SortHelper::getResultSort(t.term());
    if(sort.isArrowSort() || sort.isVar() || (sort.isBoolSort() && !topLevel)){
      return false;
    }
  }
  return true;
}

bool ApplicativeHelper::isTrue(TermList term){
  CALL("ApplicativeHelper::isTrue");
  return term.isTerm() && !term.term()->isSort() && env.signature->isFoolConstantSymbol(true, term.term()->functor());
}

bool ApplicativeHelper::isFalse(TermList term){
  CALL("ApplicativeHelper::isFalse");
  return term.isTerm() && !term.term()->isSort() && env.signature->isFoolConstantSymbol(false, term.term()->functor());
}

bool ApplicativeHelper::canHeadReduce(TermList const& head, TermStack const& args){
  CALL("ApplicativeHelper::canHeadReduce");
  
  return head.isLambdaTerm() && args.size();
}

bool ApplicativeHelper::isEtaExpandedVar(TermList t, TermList& var){
  CALL("ApplicativeHelper::isEtaExpandedVar");

  // TODO code sharing with Eta reducer above
  TermList body = t;
  unsigned l = 0; // number of lambda binders
  while(body.isLambdaTerm()){
    l++;
    body = body.lambdaBody();
  }
  
  unsigned n = 0; // number of De bruijn indices at end of term 
  while(body.isApplication()){
    auto dbIndex = body.rhs().deBruijnIndex();
    if(!dbIndex.isSome() || dbIndex.unwrap() != n)
    { break; }
    body = body.lhs();
    n++;
  }

  var = body;
  return n == l && var.isVar();
}


void ApplicativeHelper::normaliseLambdaPrefixes(TermList& t1, TermList& t2)
{
  CALL("ApplicativeHelper::normaliseLambdaPrefixes");

  if(t1.isVar() && t2.isVar()) return;
  TermList nonVar = t1.isVar() ? t2 : t1;
  TermList sort = SortHelper::getResultSort(nonVar.term());

  auto etaExpand = [](TermList t, TermList sort, TermStack& sorts, unsigned n){
    TermStack sorts1; // sorts of new prefix

    t = TermShifter().shift(t,n); // lift loose indices by n

    for(int i = n - 1; i >= 0; i--){ // append De Bruijn indices
      ASS(sort.isArrowSort());
      auto s = sort.domain();
      auto dbIndex = getDeBruijnIndex((unsigned)i,s);
      t = app(sort, t, dbIndex);
      sort = sort.result();
      sorts1.push(s);
    }

    while(!sorts1.isEmpty()){ // wrap in new lambdas
      t = lambda(sorts1.pop(), t);
    }

    while(!sorts.isEmpty()){ // wrap in original lambdas
      t = lambda(sorts.pop(), t);
    }

    return t;
  };
 
  unsigned m = 0;
  unsigned n = 0;
  TermList t1c = t1;
  TermList t2c = t2;
  TermList t1s = sort;
  TermList t2s = sort;
  TermStack prefSorts1;
  TermStack prefSorts2;
  
  while(t1c.isLambdaTerm()){
    t1c = t1c.lambdaBody();
    prefSorts1.push(t1s.domain());
    t1s = t1s.result();
    m++;
  }

  while(t2c.isLambdaTerm()){
    t2c = t2c.lambdaBody();
    prefSorts2.push(t2s.domain());
    t2s = t2s.result();    
    n++;
  }

  if(m > n)
    t2 = etaExpand(t2c, t2s, prefSorts2, m - n);

  if(n > m)
    t1 = etaExpand(t1c, t1s, prefSorts1, n - m);
}


bool ApplicativeHelper::getProjAndImitBindings(TermList flexTerm, TermList rigidTerm, TermStack& bindings,
  TermList& fVar)
{
  CALL("ApplicativeHelper::getProjAndImitBindings");

  ASS(bindings.isEmpty());

  // if flexTerm is of form X t1 t2 : i > i and t1 : int and t2 : tau
  // this function will fill stack with [i, tau, int]
  // Very inelegant at the moment, need to rewrite TODO
  auto getFlexHeadSorts = [](TermList flexTerm, TermStack& sorts, TermList rigidTermSort){
    TermList matrixSort;
    if(flexTerm.isVar()){
      matrixSort = rigidTermSort;
    } else {
      matrixSort = SortHelper::getResultSort(flexTerm.term());
      while(flexTerm.isLambdaTerm()){
        matrixSort = *flexTerm.term()->nthArgument(1);
        flexTerm = flexTerm.lambdaBody();
      }
    }

    TermStack temp;
    getArgSorts(matrixSort,temp);
    while(!temp.isEmpty()){
      sorts.push(temp.pop());
    }
    getArgSorts(flexTerm,sorts);
  };

  // since term is rigid, cannot be a variable
  TermList sort = SortHelper::getResultSort(matrix(rigidTerm).term()).finalResult();
  TermList headRigid = rigidTerm.head();
  TermList headFlex;
  TermStack argsFlex;
  TermStack sortsFlex; //sorts of arguments of flex head

  getHeadAndArgs(flexTerm, headFlex, argsFlex);
  getFlexHeadSorts(flexTerm, sortsFlex, SortHelper::getResultSort(rigidTerm.term()));

  TermList pb;
  TermList var = fVar;
  bool imit = false;
  // imitation
  if(headRigid.deBruijnIndex().isNone()){ // cannot imitate a bound variable
    imit = true;
    pb = createGeneralBinding(var, headRigid, sortsFlex);
    fVar = var.var() > fVar.var() ? var : fVar;  
    bindings.push(pb);
  }

  ASS(sortsFlex.size() >= argsFlex.size());
  unsigned diff = sortsFlex.size() - argsFlex.size();

  // projections
  for(unsigned i = 0; i < argsFlex.size(); i++){
    // try and project each of the arguments of the flex head in turn
    TermList arg = argsFlex[i];
    TermList argSort = sortsFlex[i + diff];
    // sort wrong, cannot project this arg
    if(argSort.finalResult() != sort) continue;
    TermList head = arg.head();
    // argument has a rigid head different to that of rhs. no point projecting
    if(head.isTerm() &&  head.deBruijnIndex().isNone() &&  head != headRigid) continue;

    TermList dbi = getDeBruijnIndex(i + diff, sortsFlex[i + diff]);

    TermList pb = createGeneralBinding(fVar,dbi,sortsFlex);
    fVar = var.var() > fVar.var() ? var : fVar;
    bindings.push(pb);
  }

  return imit;
}

TermList ApplicativeHelper::createGeneralBinding(TermList& freshVar, TermList head, 
  TermStack& sorts, bool surround){
  CALL("ApplicativeHelper::createGeneralBinding/3");
  ASS(head.isTerm()); // in the future may wish to reconsider this assertion

  TermStack args;
  TermStack argSorts;
  TermStack indices;    

  auto getNextFreshVar = [&](){
    freshVar = TermList(freshVar.var() + 1, freshVar.bank());
    return freshVar; 
  };

  TermList headSort = SortHelper::getResultSort(head.term());
  getArgSorts(headSort, argSorts);

  for(unsigned i = 0; i < sorts.size(); i++){
    indices.push(getDeBruijnIndex(i, sorts[i]));
  }

  while(!argSorts.isEmpty()){
    TermList varSort = AtomicSort::arrowSort(sorts, argSorts.pop());
    args.push(app(varSort, getNextFreshVar(), indices));
  }

  TermList pb = app(head, args);
  return surround ? surroundWithLambdas(pb, sorts) : pb; 
}

TermList ApplicativeHelper::surroundWithLambdas(TermList t, TermStack& sorts, bool fromTop)
{
  CALL("ApplicativeHelper::surroundWithLambdas/1");

  ASS(t.isTerm());
  TermList sort = SortHelper::getResultSort(t.term());
  return surroundWithLambdas(t, sorts, sort, fromTop);
}


TermList ApplicativeHelper::surroundWithLambdas(TermList t, TermStack& sorts, TermList sort, bool fromTop)
{
  CALL("ApplicativeHelper::surroundWithLambdas/2");

  if(!fromTop){ // TODO fromTop is very hacky. See if can merge these two into one loop
    for(unsigned i = 0; i < sorts.size(); i++)
    { 
      t = lambda(sorts[i], sort, t); 
      sort = AtomicSort::arrowSort(sorts[i], sort);
    }
  } else {
    for(int i = sorts.size() - 1; i >= 0; i--)
    { 
      t = lambda(sorts[i], sort, t);
      sort = AtomicSort::arrowSort(sorts[i], sort);       
    }    
  }
  return t;  
}

TermList ApplicativeHelper::top(){
  CALL("ApplicativeHelper::top");

  return TermList(Term::foolTrue());
}

TermList ApplicativeHelper::bottom(){
  CALL("ApplicativeHelper::bottom");

  return TermList(Term::foolFalse());
}

TermList ApplicativeHelper::conj(){
  CALL("ApplicativeHelper::conj");

  return TermList(Term::createConstant(env.signature->getBinaryProxy("vAND")));
}

TermList ApplicativeHelper::disj(){
  CALL("ApplicativeHelper::disj");

  return TermList(Term::createConstant(env.signature->getBinaryProxy("vOR")));
}

TermList ApplicativeHelper::imp(){
  CALL("ApplicativeHelper::imp");

  return TermList(Term::createConstant(env.signature->getBinaryProxy("vIMP")));
}

TermList ApplicativeHelper::neg(){
  CALL("ApplicativeHelper::neg");

  return TermList(Term::createConstant(env.signature->getNotProxy()));
} 

TermList ApplicativeHelper::equality(TermList sort){
  CALL("ApplicativeHelper::equality");

  return TermList(Term::create1(env.signature->getEqualityProxy(), sort));
}

TermList ApplicativeHelper::pi(TermList sort){
  CALL("ApplicativeHelper::pi");

  return TermList(Term::create1(env.signature->getPiSigmaProxy("vPI"), sort));
}

TermList ApplicativeHelper::sigma(TermList sort){
  CALL("ApplicativeHelper::sigma");

  return TermList(Term::create1(env.signature->getPiSigmaProxy("vSIGMA"), sort));
}

#endif