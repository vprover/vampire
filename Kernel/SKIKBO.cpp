
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

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "SKIKBO.hpp"
#include "Signature.hpp"
#include "SortHelper.hpp"
#include "ApplicativeHelper.hpp"

#define COLORED_WEIGHT_BOOST 0x10000

namespace Kernel {

using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class SKIKBO::State
{
public:
  /** Initialise the state */
  State(SKIKBO* kbo)
    : _kbo(*kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  CLASS_NAME(SKIKBO::State);
  USE_ALLOCATOR(State);

  void traverse(Term* t1, Term* t2);
  void traverse(TermList tl,int coefficient);
  Result result(Term* t1, Term* t2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList t1, TermList t2);
  Result applyVariableCondition(Result res)
  {
    if(_posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(_negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int _weightDiff;
  DHMap<unsigned, int, IdentityHash> _varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int _posNum;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  SKIKBO& _kbo;
  /** The variable counters */
}; // class KBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result SKIKBO::State::result(Term* t1, Term* t2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    if(t1->isLiteral()) {
      int prec1, prec2;
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else {
      res=_kbo.compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

  //the result should never be EQUAL:
  //- either t1 and t2 are truely equal. But then if they're equal, it
  //would have been discovered by the t1==t2 check in
  //KBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result SKIKBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("KBO::State::innerResult");

  ASS_NEQ(tl1, tl2);
  ASS(!TermList::sameTopFunctor(tl1,tl2));

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(tl1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(tl2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else {
      res=_kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void SKIKBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    } else if(*pnum==1) {
      _posNum++;
    }
  } else {
    if(*pnum==0) {
      _posNum--;
    } else if(*pnum==-1) {
      _negNum++;
    }
  }
}

void SKIKBO::State::traverse(TermList tl,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    _weightDiff+=_kbo._variableWeight*coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.functionSymbolWeight(t->functor())*coef;

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      _weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
      if(ts->term()->arity()) {
        stack.push(ts->term()->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void SKIKBO::State::traverse(Term* t1, Term* t2)
{
  CALL("KBO::State::traverse");
  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<TermList*> stack(32);
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!stack.isEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
        lexValidDepth=depth;
        if(_weightDiff!=0) {
          _lexResult=_weightDiff>0 ? GREATER : LESS;
        }
        _lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      ASS(ss->term()->arity());
      stack.push(ss->term()->args());
      stack.push(tt->term()->args());
      depth++;
    } else {
      traverse(*ss,1);
      traverse(*tt,-1);
      if(_lexResult==EQUAL) {
        _lexResult=innerResult(*ss, *tt);
        lexValidDepth=depth;
        ASS(_lexResult!=EQUAL);
        ASS(_lexResult!=GREATER_EQ);
        ASS(_lexResult!=LESS_EQ);
      }
    }
  }
  ASS_EQ(depth,0);
}


/**
 * Create a KBO object.
 */
SKIKBO::SKIKBO(Problem& prb, const Options& opt)
 : PrecedenceOrdering(prb, opt)
{
  CALL("SKIKBO::SKIKBO");

  _variableWeight = 1;
  _defaultSymbolWeight = 1;

  _state=new State(this);
}

SKIKBO::~SKIKBO()
{
  CALL("SKIKBO::~SKIKBO");

  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result SKIKBO::comparePredicates(Literal* l1, Literal* l2) const
{
  CALL("KBO::comparePredicates");
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  Result res;
  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif
  state->init();
  if(p1!=p2) {
    TermList* ts;
    ts=l1->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,1);
      ts=ts->next();
    }
    ts=l2->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,-1);
      ts=ts->next();
    }
  } else {
    state->traverse(l1,l2);
  }

  res=state->result(l1,l2);
#if VDEBUG
  _state=state;
#endif
  return res;
} // KBO::comparePredicates()

Ordering::Result SKIKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
    }
  }
  if(tl2.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
    }
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();
 
  if(t1->maxRedLength() == -1){ t1->setMaxRedLen(maximumReductionLength(t1)); }
  if(t2->maxRedLength() == -1){ t2->setMaxRedLen(maximumReductionLength(t2)); }
 
  if(t1->maxRedLength() > t2->maxRedLength()){
    return GREATER;
  } else if (t2->maxRedLength() > t1->maxRedLength()){
    return LESS;
  }

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(t1->functor()==t2->functor()) {
    state->traverse(t1,t2);
  } else {
    state->traverse(tl1,1);
    state->traverse(tl2,-1);
  }
  Result res=state->result(t1,t2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

int SKIKBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;

  if(env.signature->functionColored(fun)) {
    weight *= COLORED_WEIGHT_BOOST;
  }

  return weight;
}


unsigned SKIKBO::maximumReductionLength(TermList term)
{
  CALL("SKIKBO::maximumReductionLength");  
   
  typedef ApplicativeHelper AH;
  typedef SortHelper SH;  
  
  static TermStack toEvaluate;
  static TermStack args;
  TermList head;
  unsigned length = 0;

  toEvaluate.push(term);
  while(!toEvaluate.isEmpty()){
    args.reset(); 
    TermList evaluating = toEvaluate.pop();
    AH::getHeadAndArgs(evaluating, head, args);
    if(head.isVar() || !AH::isComb(head)){
      while(!args.isEmpty()){
        toEvaluate.push(args.pop());
      }
    } else {
      Signature::Combinator c = AH::getComb(head);
      TermList newHeadSort = AH::getNthArg(SH::getResultSort(head.term()), 1);
      if(c == Signature::I_COMB){
        toEvaluate.push(AH::createAppTerm(newHeadSort, args.pop(), args));//working on the assumption that the pop happens first...
        length++;
      } else if(c == Signature::K_COMB){
        TermList newHead = args.pop();
        toEvaluate.push(args.pop()); 
        toEvaluate.push(AH::createAppTerm(newHeadSort, newHead, args));
        length++;
      } else {
        length++;
        toEvaluate.push(reduce(args, head));
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
