
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
    _varTermDiffs.reset();
  }

  CLASS_NAME(SKIKBO::State);
  USE_ALLOCATOR(State);

  void traverse(ApplicativeArgsIt& aai1, ApplicativeArgsIt& aai2);
  void traverse(ApplicativeArgsIt& aai, int coefficient);
  Result result(ApplicativeArgsIt& aai1, ApplicativeArgsIt& aai2);
private:
  void recordVariable(TermList var, int coef);
  Result innerResult(ApplicativeArgsIt& aai1, ApplicativeArgsIt& aai2);
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
  DHMap<Term*, int> _varTermDiffs;
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
Ordering::Result SKIKBO::State::result(ApplicativeArgsIt& aai1, ApplicativeArgsIt& aai2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(aai1.head()!=aai2.head()) {
    res=_kbo.compareFunctionPrecedences(aai1.head().term()->functor(), aai2.head().term()->functor());
    ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  //ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

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

Ordering::Result SKIKBO::State::innerResult(ApplicativeArgsIt& aai1, ApplicativeArgsIt& aai2)
{
  CALL("KBO::State::innerResult");

  ASS(aai1.head() != aai2.head());

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(aai1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(aai2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else {
      res=_kbo.compareFunctionPrecedences(aai1.head().term()->functor(), aai2.head().term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void SKIKBO::State::recordVariable(TermList var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  if(var.isVar()){
    _varDiffs.getValuePtr(var.var(),pnum,0);
  } else {
    _varTermDiffs.getValuePtr(var.term(),pnum,0);
  }
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

void SKIKBO::State::traverse(ApplicativeArgsIt& aai,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  //we know that the head is not a variable
  _weightDiff+=_kbo.functionSymbolWeight(aai.head().term()->functor())*coef;

  if(!aai.hasNext()) {
    return;
  }

  static Stack<ApplicativeArgsIt*> stack(4);
  stack.push(&aai);
  for(;;) {
    TermList ts = stack.top()->next();
    ApplicativeArgsIt aai1(ts);
    if(aai1.isVar()){
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts, coef);      
    } else {
      _weightDiff+=_kbo.functionSymbolWeight(aai1.head().term()->functor())*coef;
      if(aai1.hasNext()) {
        stack.push(&aai1);
      }
    }
    while(!stack.top()->hasNext()){
      stack.pop();
      if(stack.isEmpty()) {
        break;
      }
    }
  }
}

void SKIKBO::State::traverse(ApplicativeArgsIt& aat1, ApplicativeArgsIt& aat2)
{
  CALL("KBO::State::traverse");
  ASS(aat1.head()==aat2.head());
  ASS(aat1.hasNext());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<ApplicativeArgsIt*> stack(32);
  stack.push(&aat1);
  stack.push(&aat2);
  TermList ss; //t1 subterms
  TermList tt; //t2 subterms
  while(!stack.isEmpty()) {
    if(!stack.top()->hasNext() || !stack.scnd()->hasNext()){
      ASS((stack.top()->hasNext() && !stack.scnd()->hasNext()) || depth == 1);
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
        lexValidDepth=depth;
        if(_weightDiff!=0) {
          _lexResult=_weightDiff>0 ? GREATER : LESS;
        }
        _lexResult=applyVariableCondition(_lexResult);
      }
      continue;
      stack.pop();
      stack.pop();
    }
    ss = stack.top()->next();
    tt = stack.scnd()->next();

    if(ss.sameContent(&tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    ApplicativeArgsIt aai1(ss);
    ApplicativeArgsIt aai2(tt);
    if(!(aai1.isVar() || aai2.isVar()) && aai1.head() == aai2.head()) {
      ASS(aai1.hasNext());
      ASS(aai2.hasNext());
      stack.push(&aai1);
      stack.push(&aai2);
      depth++;
    } else {
      if(aai1.isVar()){
        _weightDiff+=_kbo._variableWeight*1; //all variables 1, even applied variables with args
        recordVariable(ss, 1);
      } else {
        traverse(aai1,1);
      }
      if(aai2.isVar()){
        _weightDiff+=_kbo._variableWeight*-1; //all variables 1, even applied variables with args
        recordVariable(tt, -1);
      } else {
        traverse(aai2,-1);
      }
      if(_lexResult==EQUAL) {
        _lexResult=innerResult(aai1, aai2);
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


VarCondRes SKIKBO::compareVariables(TermList tl1, TermList tl2)
{
  CALL("SKIKBO::compareVariables");

  DHMultiset<unsigned> tl1Vars;
  DHMultiset<Term*> tl1UnstableTerms;
  DHMap<Term*, ArgsReductionData*> tl1RedData;
  DHMultiset<unsigned> tl2Vars;
  DHMultiset<Term*> tl2UnstableTerms;

  if(tl1.isVar()){
    tl1Vars.insert(tl1.var());
  } else {
    //TODO could be not a term
    UnstableSubTermIt usti(tl1.term());
    while(usti.hasNext()){
      tl1UnstableTerms.insert(usti.next());
    }
    StableVarIt svi(tl1.term(), tl1UnstableTerms);
    while(svi.hasNext()){
      TermList tl = svi.next();
      if(tl.isVar()){
        tl1Vars.insert(tl.var());
      } else {
        
      }
    }
  }

}

Ordering::Result SKIKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }

  varCond = compareVariables(tl1, tl2);
  if(varCond != INCOMP){
    if(varCond == LEFT){
      
    } else if (varCond == RIGHT) {

    }

  }
  return INCOMPARABLE;

  ApplicativeArgsIt aat1(tl1);
  ApplicativeArgsIt aat2(tl2);

  if(aat1.isVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
    }
  }
  if(aat2.isVar()) {
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
  if(aat1.head()==aat2.head()) {
    state->traverse(aat1,aat2);
  } else {
    state->traverse(aat1,1);
    state->traverse(aat2,-1);
  }
  Result res=state->result(aat1,aat2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

int SKIKBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;

  return weight;
}


unsigned SKIKBO::maximumReductionLength(Term* term)
{
  CALL("SKIKBO::maximumReductionLength");  
   
  typedef ApplicativeHelper AH;
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
    if(head.isVar() || !AH::isComb(head) || AH::isUnderApplied(head, args.size())){
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
