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

  void traverse(ArgsIt_ptr aai1, ArgsIt_ptr aai2);
  void traverse(ArgsIt_ptr aai, int coefficient);
  Result result(ArgsIt_ptr aai1, ArgsIt_ptr aai2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(ArgsIt_ptr aai1, ArgsIt_ptr aai2);
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
  DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
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
Ordering::Result SKIKBO::State::result(ArgsIt_ptr aai1, ArgsIt_ptr aai2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(!_kbo.sameCategoryHeads(aai1, aai2) || aai1->headNum()!=aai2->headNum()) {
    if(aai1->varHead() || aai2->varHead()){ //TODO extend to mghds
      return INCOMPARABLE;
    } else {
      res=_kbo.compareFunctionPrecedences(aai1->headNum(), aai2->headNum());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
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

Ordering::Result SKIKBO::State::innerResult(ArgsIt_ptr aai1, ArgsIt_ptr aai2)
{
  CALL("KBO::State::innerResult");

  ASS(!_kbo.sameCategoryHeads(aai1, aai2) || aai1->headNum() != aai2->headNum());

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(aai1->isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(aai2->isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else {
      if(aai1->varHead() || aai2->varHead()){//TODO extend to mghds
        return INCOMPARABLE;
      } 
      res=_kbo.compareFunctionPrecedences(aai1->headNum(), aai2->headNum());
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

void SKIKBO::State::traverse(ArgsIt_ptr aai,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(!aai->varHead()){
    _weightDiff+=_kbo.symbolWeight(aai->head().term())*coef;
  } else {
    _weightDiff+=_kbo._weights._specialWeights._variableWeight*coef;
    recordVariable(aai->headNum(), coef);
  }

  if(!aai->hasNext()) {
    return;
  }
  static Stack<ArgsIt_ptr> stack(4);
  stack.push(aai);
  while(!stack.isEmpty()) {
    TermList ts = stack.top()->next();
    ArgsIt_ptr aai1 = ArgsIt_ptr(new ApplicativeArgsIt(ts));
    if(aai1->varHead()){
      _weightDiff+=_kbo._weights._specialWeights._variableWeight*coef;
      recordVariable(aai1->headNum(), coef);
    } else {
      _weightDiff+=_kbo.symbolWeight(aai1->head().term())*coef;
    }
    if(aai1->hasNext()) {
      stack.push(aai1);
    }
    while(!stack.isEmpty() && !stack.top()->hasNext()){
      stack.pop();
    }
  }
}

void SKIKBO::State::traverse(ArgsIt_ptr aat1, ArgsIt_ptr aat2)
{
  CALL("KBO::State::traverse");
  ASS(aat1->headNum()==aat2->headNum());
  ASS(aat1->hasNext() || aat2->hasNext());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<ArgsIt_ptr> stack(32);
  stack.push(aat2);
  stack.push(aat1);
  TermList ss; //t1 subterms
  TermList tt; //t2 subterms
  while(!stack.isEmpty()) {
    if(!stack.top()->hasNext() && !stack.scnd()->hasNext()){
      ASS_NEQ(_lexResult,EQUAL);     
      depth--;
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
        lexValidDepth=depth;
        if(_weightDiff!=0) {
          _lexResult=_weightDiff>0 ? GREATER : LESS;
        }
        _lexResult=applyVariableCondition(_lexResult);
      }
      stack.pop();
      stack.pop();
      continue;
    }
    bool topHasNext = stack.top()->hasNext();
    bool scdHasNext = stack.scnd()->hasNext();
    bool bthHaveNext = topHasNext && scdHasNext;

    if(topHasNext){ ss = stack.top()->next(); }
    if(scdHasNext){ tt = stack.scnd()->next(); }

    if(bthHaveNext && ss.sameContent(&tt)) {
      continue;
    }

    ArgsIt_ptr aai1;
    if(bthHaveNext || topHasNext){ aai1 = ArgsIt_ptr(new ApplicativeArgsIt(ss)); }
    ArgsIt_ptr aai2;
    if(bthHaveNext || scdHasNext){ aai2 = ArgsIt_ptr(new ApplicativeArgsIt(tt)); }

    if(!bthHaveNext && topHasNext){
      _lexResult = GREATER; //using length-lexicographic ordering
      traverse(aai1,1);
      continue;
    }

    if(!bthHaveNext && scdHasNext){
      _lexResult = LESS;  //using length-lexicographic ordering 
      traverse(aai2,-1);
      continue;
    }

    if(_kbo.sameCategoryHeads(aai1, aai2) && aai1->headNum() == aai2->headNum()) {
      ASS(aai1->hasNext() || aai2->hasNext());
      stack.push(aai2);
      stack.push(aai1);
      depth++;
    } else {
      traverse(aai1,1);
      traverse(aai2,-1);
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
 * Create a SKIKBO object.
 */
SKIKBO::SKIKBO(Problem& prb, const Options& opt, bool basic_hol)
 : PrecedenceOrdering(prb, opt),
   _weights(KboWeightMap<FuncSigTraits>::dflt())
{
  CALL("SKIKBO::SKIKBO");

  _state=new State(this);
  _basic_hol = basic_hol;
}

SKIKBO::SKIKBO(
  KboWeightMap<FuncSigTraits> symbolWeights, 

  // precedence ordering params
  DArray<int> funcPrec, 
  DArray<int> typeConPrec,
  DArray<int> predPrec, 
  DArray<int> predLevels, 

  // other
  bool reverseLCM
  ) : PrecedenceOrdering(funcPrec, typeConPrec, predPrec, predLevels, reverseLCM)
  , _weights(symbolWeights)
  , _state(new State(this))
  , _basic_hol(0)
{ }

SKIKBO::~SKIKBO()
{
  CALL("SKIKBO::~SKIKBO");
  delete _state;
}

bool SKIKBO::safe(Term* t1, Term* t2) const 
{
  CALL("SKIKBO::safe");

  static TermStack toBeChecked;
  toBeChecked.push(TermList(t1));
  toBeChecked.push(TermList(t2));

  while(!toBeChecked.isEmpty()){
    TermList term1 = toBeChecked.pop();
    TermList term2 = toBeChecked.pop();

    if(term1.isVar() || term2.isVar()){
      if(term1 != term2){
        return false;
      } else {
        continue;
      }
    }
    
    if((AH::isComb(term1) && !AH::isComb(term2)) ||
       (AH::isComb(term2) && !AH::isComb(term1)) ||
       (AH::isComb(term1) && AH::isComb(term2) && AH::getComb(term1) != AH::getComb(term2))){
      return false;
    } else if(AH::isComb(term2) && AH::isComb(term1)){
      continue;
    }

    if(!term1.term()->hasTermVar() && !term2.term()->hasTermVar()){
      TermList head1 = AH::getHead(term1);
      TermList head2 = AH::getHead(term2);
      if(!AH::isComb(head1) && !AH::isComb(head2)){
        if(maximumReductionLength(term2.term()) > maximumReductionLength(term1.term())){
          return false;
        } else {
          continue;
        }
      } else {
        return false;
      }
    } else if (!term1.term()->hasTermVar() || !term2.term()->hasTermVar()){
      // early failure, it is impossible for these terms to be safe
      // e.g. (f X) and g. 
      return false;
    }

    //cout << term1.toString() << endl;
    //cout << term2.toString() << endl;

    toBeChecked.push(*term1.term()->nthArgument(2));
    toBeChecked.push(*term2.term()->nthArgument(2));
    toBeChecked.push(*term1.term()->nthArgument(3));
    toBeChecked.push(*term2.term()->nthArgument(3));
  }
  return true;
}

/** A linear time approximation of the actual variable condition from the paper */
bool SKIKBO::varConditionHolds(DHMultiset<Term*>& tlTerms1, DHMultiset<Term*>& tlTerms2) const
{
  CALL("SKIKBO::varConditionHolds");

  DHMultiset<Term*> unmatchedTlTerms1;
  unmatchedTlTerms1.loadFromIterator(DHMultiset<Term*>::Iterator(tlTerms1));

  DHMultiset<Term*>::Iterator it(tlTerms2);
  while(it.hasNext()){
    Term* term = it.next();
    bool matchFound = false;
    DHMultiset<Term*>::Iterator it2(tlTerms1);
    while(it2.hasNext()){
      Term* term2 = it2.next();
      if(safe(term, term2)){
        unmatchedTlTerms1.remove(term2);
        matchFound = true;
        break;
      }
    }
    if(!matchFound){
      return false;
    }
  }
  
  return true;
}

SKIKBO::VarCondRes SKIKBO::compareVariables(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compareVariables");

  VarCondRes vcr = BOTH;

  DHMultiset<Term*> tl1TopLevelVarLikeTerms;
  DHMultiset<Term*> tl2TopLevelVarLikeTerms;

  if(!tl1.isVar()){
    TopLevelVarLikeTermIterator usti(tl1.term());
    while(usti.hasNext()){
      tl1TopLevelVarLikeTerms.insert(usti.next());
    }
  }

  if(!tl2.isVar()){
    TopLevelVarLikeTermIterator usti(tl2.term());
    while(usti.hasNext()){
      tl2TopLevelVarLikeTerms.insert(usti.next());
    }
  }

  if(tl1TopLevelVarLikeTerms.size() > tl2TopLevelVarLikeTerms.size()){
    vcr = LEFT;
  } else if (tl2TopLevelVarLikeTerms.size() > tl1TopLevelVarLikeTerms.size()){
    vcr = RIGHT;
  }

  if(env.options->complexVarCondition()){
    if(vcr == BOTH || vcr == LEFT){

      bool vcHolds = varConditionHolds(tl1TopLevelVarLikeTerms, tl2TopLevelVarLikeTerms);
      if(!vcHolds){
        if(vcr == BOTH){
          vcr = RIGHT;
        } else {
          return INCOMP;
        }
      }
    }
    
    if(vcr == BOTH || vcr == RIGHT){
      bool vcHolds = varConditionHolds(tl2TopLevelVarLikeTerms, tl1TopLevelVarLikeTerms);
      if(!vcHolds){
        if(vcr == BOTH){
          vcr = LEFT;
        } else {
          return INCOMP;
        }
      }
    }

  } else {
    DHMultiset<Term*>::SetIterator tl1utit(tl1TopLevelVarLikeTerms);
    while(tl1utit.hasNext()){
      unsigned tl1Mult = 0;
      Term* t = tl1utit.next(tl1Mult);
      unsigned tl2Mult = tl2TopLevelVarLikeTerms.multiplicity(t);
      if(tl1Mult > tl2Mult && vcr != RIGHT){
        vcr = LEFT;
      } else if(tl2Mult > tl1Mult && vcr != LEFT){
        vcr = RIGHT;
      } else if (tl1Mult != tl2Mult){
        return INCOMP;
      }
    }

    DHMultiset<Term*>::SetIterator tl2utit(tl2TopLevelVarLikeTerms);
    while(tl2utit.hasNext()){
      unsigned tl2Mult = 0;
      Term* t = tl2utit.next(tl2Mult);
      unsigned tl1Mult = tl1TopLevelVarLikeTerms.multiplicity(t);
      if(tl1Mult > tl2Mult && vcr != RIGHT){
        vcr = LEFT;
      } else if(tl2Mult > tl1Mult && vcr != LEFT){
        vcr = RIGHT;
      } else if (tl1Mult != tl2Mult){
        return INCOMP;
      }
    }
  }

  DHMultiset<unsigned> tl1TopLevelVars;
  TopLevelVarIterator svi(tl1);
  while(svi.hasNext()){
    TermList tl = svi.next();
    ASS(tl.isVar());
    tl1TopLevelVars.insert(tl.var());
  }

  DHMultiset<unsigned> tl2TopLevelVars;
  TopLevelVarIterator svi2(tl2);
  while(svi2.hasNext()){
    TermList tl = svi2.next();
    ASS(tl.isVar());
    tl2TopLevelVars.insert(tl.var());
  }

  if(tl1TopLevelVars.size() > tl2TopLevelVars.size() && vcr != RIGHT){
    vcr = LEFT;
  } else if (tl2TopLevelVars.size() > tl1TopLevelVars.size()  && vcr != LEFT){
    vcr = RIGHT;
  } else if(tl1TopLevelVars.size() != tl2TopLevelVars.size()){
    return INCOMP;
  }


  DHMultiset<unsigned>::SetIterator tl1vit(tl1TopLevelVars);
  while(tl1vit.hasNext()){
    unsigned tl1Mult = 0;
    unsigned var = tl1vit.next(tl1Mult);
    unsigned tl2Mult = tl2TopLevelVars.multiplicity(var);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<unsigned>::SetIterator tl2vit(tl2TopLevelVars);
  while(tl2vit.hasNext()){
    unsigned tl2Mult = 0;
    unsigned var = tl2vit.next(tl2Mult);
    unsigned tl1Mult = tl1TopLevelVars.multiplicity(var);
    //cout << "its multip on right is " << tl1Mult << endl;
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  return vcr;
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
  ASS(tRedLen >= 0);
  return (unsigned)tRedLen;
}


Ordering::Result SKIKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compare(TermList)");

  //bool print = false;
  if(tl1==tl2) {
    return EQUAL;
  }

  bool bothGround = tl1.isTerm() && tl1.term()->ground() && tl2.isTerm() && tl2.term()->ground();

  if(bothGround && tl1.containsSubterm(tl2)){
    return GREATER;
  }

  if(bothGround && tl2.containsSubterm(tl1)){
    return LESS;
  }
 
  ArgsIt_ptr aat1 = ArgsIt_ptr(new ApplicativeArgsIt(tl1));
  ArgsIt_ptr aat2 = ArgsIt_ptr(new ApplicativeArgsIt(tl2));

  if(!_basic_hol){
    VarCondRes varCond = compareVariables(tl1, tl2);

    if(varCond == INCOMP){ 
      return INCOMPARABLE; 
    }

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

    if(aat1->isVar() && (varCond == RIGHT || varCond == BOTH)){ //TODO unary function weight 1
      return LESS; 
    } else if(aat1->isVar() ) {
      return INCOMPARABLE;
    }

    if(aat2->isVar() && (varCond == LEFT || varCond == BOTH)) {
      return GREATER;
    } else if(aat2->isVar() ) {
      return INCOMPARABLE;
    }
  }

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(sameCategoryHeads(aat1, aat2) && aat1->headNum()==aat2->headNum()) {
    state->traverse(aat1,aat2);
  } else {
    state->traverse(aat1,1);
    state->traverse(aat2,-1);
  }
  Result res=state->result(aat1,aat2);
  /*if(print){
    if(res == LESS){ cout << tl1.toString() + " < " + tl2.toString() << endl; }
    if(res == GREATER){ cout << tl1.toString() + " > " + tl2.toString() << endl; }
    if(res == INCOMPARABLE){ cout << tl1.toString() + " <> " + tl2.toString() << endl; }
  }*/
#if VDEBUG
  _state=state;
#endif
  return res;
}

int SKIKBO::symbolWeight(Term* t) const
{
  if (t->isSort()){
    //For now just give all type constructors minimal weight
    return _weights._specialWeights._variableWeight;
  }
  return _weights.symbolWeight(t);
}


unsigned SKIKBO::maximumReductionLength(Term* term)

{  CALL("SKIKBO::maximumReductionLength");  
       
  static Stack<Term*> toEvaluate;
  static TermStack args;
  TermList head;
  unsigned length = 0;

  toEvaluate.push(term);
  while(!toEvaluate.isEmpty()){
    args.reset(); 
    Term* evaluating = toEvaluate.pop();
    AH::getHeadAndArgs(evaluating, head, args);
    if(!AH::isComb(head) || AH::isUnderApplied(head, args.size())){
      while(!args.isEmpty()){
        TermList t = args.pop();
        if(!t.isVar()){
          toEvaluate.push(t.term());
        }
      }
    } else {
      if(AH::getComb(head) == Signature::K_COMB){
        TermList t = args[args.size()-2];
        if(!t.isVar()){
          toEvaluate.push(t.term());
        }
      }
      TermList t = reduce(args, head);
      if(!t.isVar()){
        toEvaluate.push(t.term());
      }
      length++;
    }
  }
  return length;
}

TermList SKIKBO::reduce(TermStack& args, TermList& head)
{
  CALL("SKIKBO::reduce");
  
  ASS(head.isTerm());
  Signature::Combinator c = AH::getComb(head);
  ASS(c != Signature::NOT_COMB);
  
  TermList headSort = SortHelper::getResultSort(head.term());
  
  TermList newHeadSort = ApplicativeHelper::getNthArg(headSort, 1);

  TermList newHead = args.pop();
  TermList y, z, sort2;

  if(c != Signature::I_COMB){
    sort2 = ApplicativeHelper::getNthArg(headSort, 2);
    y = args.pop();
    if(c != Signature::K_COMB){
      z = args.pop();
    }
  }
  switch(c){
    case Signature::I_COMB:
    case Signature::K_COMB:
      break;
    case Signature::C_COMB: {
      args.push(y);
      args.push(z);
      break;
    }
    case Signature::B_COMB: {
      args.push(ApplicativeHelper::createAppTerm(sort2, y, z));
      break;      
    }
    case Signature::S_COMB: {
      args.push(ApplicativeHelper::createAppTerm(sort2, y, z));
      args.push(z);
      break;
    }
    default:
      ASSERTION_VIOLATION; 
  }
  return ApplicativeHelper::createAppTerm(newHeadSort, newHead, args);
}


}
