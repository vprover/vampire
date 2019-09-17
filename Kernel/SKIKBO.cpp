
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

  void traverse(ApplicativeArgsIt* aai1, ApplicativeArgsIt* aai2);
  void traverse(ApplicativeArgsIt* aai, int coefficient);
  Result result(ApplicativeArgsIt* aai1, ApplicativeArgsIt* aai2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(ApplicativeArgsIt* aai1, ApplicativeArgsIt* aai2);
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
Ordering::Result SKIKBO::State::result(ApplicativeArgsIt* aai1, ApplicativeArgsIt* aai2)
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

Ordering::Result SKIKBO::State::innerResult(ApplicativeArgsIt* aai1, ApplicativeArgsIt* aai2)
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

void SKIKBO::State::traverse(ApplicativeArgsIt* aai,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(!aai->varHead()){
    _weightDiff+=_kbo.functionSymbolWeight(aai->headNum())*coef;
  } else {
    _weightDiff+=_kbo._variableWeight*coef;
    recordVariable(aai->headNum(), coef);
  }

  if(!aai->hasNext()) {
    return;
  }
  static Stack<ApplicativeArgsIt*> stack(4);
  stack.push(aai);
  while(!stack.isEmpty()) {
    TermList ts = stack.top()->next();
    ApplicativeArgsIt* aai1 = new ApplicativeArgsIt(ts);
    if(aai1->varHead()){
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(aai1->headNum(), coef);
    } else {
      _weightDiff+=_kbo.functionSymbolWeight(aai1->headNum())*coef;
    }
    if(aai1->hasNext()) {
      stack.push(aai1);
    }
    while(!stack.isEmpty() && !stack.top()->hasNext()){
      if(!stack.size() == 1){ delete stack.pop(); }
      else{ stack.pop(); }
    }
  }
}

void SKIKBO::State::traverse(ApplicativeArgsIt* aat1, ApplicativeArgsIt* aat2)
{
  CALL("KBO::State::traverse");
  ASS(aat1->headNum()==aat2->headNum());
  ASS(aat1->hasNext());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<ApplicativeArgsIt*> stack(32);
  stack.push(aat2);
  stack.push(aat1);
  TermList ss; //t1 subterms
  TermList tt; //t2 subterms
  while(!stack.isEmpty()) {
    if(!stack.top()->hasNext() || !stack.scnd()->hasNext()){
      ASS_NEQ(_lexResult,EQUAL);
      if(stack.top()->hasNext()){ _lexResult = LESS; } //using length lexicorgraphic ordering f t1 t2 > f t3 always
      if(stack.scnd()->hasNext()){ _lexResult = GREATER; }      
      depth--;
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
        lexValidDepth=depth;
        if(_weightDiff!=0) {
          _lexResult=_weightDiff>0 ? GREATER : LESS;
        }
        _lexResult=applyVariableCondition(_lexResult);
      }
      delete stack.pop();
      delete stack.pop();
      continue;
    }
    ss = stack.top()->next();
    tt = stack.scnd()->next();

    if(ss.sameContent(&tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    ApplicativeArgsIt* aai1 = new ApplicativeArgsIt(ss);
    ApplicativeArgsIt* aai2 = new ApplicativeArgsIt(tt); //TODO memory leaks
    if(_kbo.sameCategoryHeads(aai1, aai2) && aai1->headNum() == aai2->headNum()) {
      ASS(aai1->hasNext());
      ASS(aai2->hasNext());
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
      delete aai1;
      delete aai2;
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


SKIKBO::VarCondRes SKIKBO::compareVariables(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compareVariables");

  VarCondRes vcr = BOTH;

  DHMultiset<Term*> tl1UnstableTerms;
  VarOccMap tl1RedData;
  DHMultiset<Term*> tl2UnstableTerms;
  VarOccMap tl2RedData;

  if(!tl1.isVar()){
    UnstableSubtermIt usti(tl1.term());
    while(usti.hasNext()){
      tl1UnstableTerms.insert(usti.next());
    }
  }

  if(!tl2.isVar()){
    UnstableSubtermIt usti(tl2.term());
    while(usti.hasNext()){
      tl2UnstableTerms.insert(usti.next());
    }
  }

  if(tl1UnstableTerms.size() > tl2UnstableTerms.size()){
    vcr = LEFT;
  } else if (tl2UnstableTerms.size() > tl1UnstableTerms.size()){
    vcr = RIGHT;
  }

  DHMultiset<Term*>::SetIterator tl1utit(tl1UnstableTerms);
  while(tl1utit.hasNext()){
    unsigned tl1Mult = 0;
    Term* t = tl1utit.next(tl1Mult);
    unsigned tl2Mult = tl2UnstableTerms.multiplicity(t);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<Term*>::SetIterator tl2utit(tl2UnstableTerms);
  while(tl2utit.hasNext()){
    unsigned tl2Mult = 0;
    Term* t = tl2utit.next(tl2Mult);
    unsigned tl1Mult = tl1UnstableTerms.multiplicity(t);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<unsigned> tl1vars;
  StableVarIt svi(tl1, &tl1UnstableTerms);
  while(svi.hasNext()){
    TermList tl = svi.next();
    TermList head = ApplicativeHelper::getHead(tl);
    ASS(head.isVar());
    tl1vars.insert(head.var());
  }

  DHMultiset<unsigned> tl2vars;
  StableVarIt svi2(tl2, &tl2UnstableTerms);
  while(svi2.hasNext()){
    TermList tl = svi2.next();
    TermList head = ApplicativeHelper::getHead(tl);
    ASS(head.isVar());
    tl2vars.insert(head.var());
  }

  if(tl1vars.size() > tl2vars.size() && vcr != RIGHT){
    vcr = LEFT;
  } else if (tl2vars.size() > tl1vars.size()  && vcr != LEFT){
    vcr = RIGHT;
  } else if(tl1vars.size() != tl2vars.size()){
    return INCOMP;
  }


  DHMultiset<unsigned>::SetIterator tl1vit(tl1vars);
  while(tl1vit.hasNext()){
    unsigned tl1Mult = 0;
    unsigned var = tl1vit.next(tl1Mult);
    unsigned tl2Mult = tl2vars.multiplicity(var);
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMultiset<unsigned>::SetIterator tl2vit(tl2vars);
  while(tl2vit.hasNext()){
    unsigned tl2Mult = 0;
    unsigned var = tl2vit.next(tl2Mult);
    unsigned tl1Mult = tl1vars.multiplicity(var);
    //cout << "its multip on right is " << tl1Mult << endl;
    if(tl1Mult > tl2Mult && vcr != RIGHT){
      vcr = LEFT;
    } else if(tl2Mult > tl1Mult && vcr != LEFT){
      vcr = RIGHT;
    } else if (tl1Mult != tl2Mult){
      return INCOMP;
    }
  }

  DHMap<unsigned, unsigned> varCounts;
  static TermStack args;
  StableVarIt svi3(tl1, &tl1UnstableTerms);
  while(svi3.hasNext()){
    args.reset(); //TODO required?
    TermList tl = svi3.next();
    TermList head;
    ApplicativeHelper::getHeadAndArgs(tl, head, args);
    ASS(head.isVar());
    unsigned var = head.var();
    DArray<DArray<unsigned>*>* vData;
    unsigned count;
    if(tl1RedData.find(var)){
      vData = tl1RedData.get(var);
      count = varCounts.get(var);
    } else {
      vData = new DArray<DArray<unsigned>*>(tl1vars.multiplicity(var));
      count = 0;
      tl1RedData.set(var, vData);
    }
    varCounts.set(var, count + 1);
    (*vData)[count] = new DArray<unsigned>(args.size());
    for(unsigned i = 0; i < args.size(); i++){
      (*(*vData)[count])[i] = getMaxRedLength(args.pop());
    }
  }

  varCounts.reset();
  StableVarIt svi4(tl2, &tl2UnstableTerms);
  while(svi4.hasNext()){
    args.reset(); //TODO required?
    TermList tl = svi4.next();
    TermList head;
    ApplicativeHelper::getHeadAndArgs(tl, head, args);
    ASS(head.isVar());
    unsigned var = head.var();
    DArray<DArray<unsigned>*>* vData;
    unsigned count;
    if(tl2RedData.find(var)){
      vData = tl2RedData.get(var);
      count = varCounts.get(var);
    } else {
      vData = new DArray<DArray<unsigned>*>(tl2vars.multiplicity(var));
      count = 0;
      tl2RedData.set(var, vData);
    }
    varCounts.set(var, count + 1);
    (*vData)[count] = new DArray<unsigned>(args.size()); //TODO why does this not trigger allocator bug?
    for(unsigned i = 0; i < args.size(); i++){
      (*(*vData)[count])[i] = getMaxRedLength(args.pop());
    }
  }

  vcr =  compareVariables(tl1RedData, tl2RedData, vcr);
  freeMem(tl1RedData, tl2RedData);
  return vcr;
}

SKIKBO::VarCondRes SKIKBO::compareVariables(VarOccMap& vomtl1 , VarOccMap& vomtl2, VarCondRes currStat) const
{
  CALL("SKIKBO::compareVariables/2");

  if(currStat == LEFT || currStat == BOTH){
    VarOccMap::Iterator it1(vomtl2);
    while(it1.hasNext()){
      unsigned var;
      DArray<DArray<unsigned>*>* arrtl2 = it1.nextRef(var);
      ASS_REP(vomtl1.find(var), "X" + Int::toString(var));
      DArray<DArray<unsigned>*>* arrtl1 = vomtl1.get(var); //returned by ref
      
      unsigned m = arrtl2->size();
      unsigned n = arrtl1->size();

      DArray<DArray<bool>> bpGraph;
      bpGraph.ensure(m);
      for(unsigned i = 0; i < m; i++){
        DArray<unsigned>* redLengths2 = (*arrtl2)[i]; 
        bpGraph[i].ensure(n);
        for(unsigned j = 0; j < n; j++){
          DArray<unsigned>* redLengths1 = (*arrtl1)[j]; 
          bpGraph[i][j] = canBeMatched(redLengths2, redLengths1);
        }
      }
      if(!totalBMP(m, n, bpGraph)){
        if(currStat == LEFT){ return INCOMP; }
        currStat = RIGHT;
        break;
      }
    }
  }
  
  if(currStat == LEFT){ return LEFT; }

  VarOccMap::Iterator it2(vomtl1);
  while(it2.hasNext()){
    unsigned var;
    DArray<DArray<unsigned>*>* arrtl1 = it2.nextRef(var);
    ASS(vomtl2.find(var));
    DArray<DArray<unsigned>*>* arrtl2 = vomtl2.get(var); //returned by ref
    
    unsigned m = arrtl1->size();
    unsigned n = arrtl2->size();

    DArray<DArray<bool>> bpGraph;
    bpGraph.ensure(m);
    for(unsigned i = 0; i < m; i++){
      DArray<unsigned>* redLengths2 = (*arrtl1)[i]; 
      bpGraph[i].ensure(n);
      for(unsigned j = 0; j < n; j++){
        DArray<unsigned>* redLengths1 = (*arrtl2)[j]; 
        bpGraph[i][j] = canBeMatched(redLengths2, redLengths1);
      }
    }
    if(!totalBMP(m, n, bpGraph)){
      if(currStat == RIGHT){ return INCOMP; }
      currStat = LEFT;
      break;
    }
  }
  return currStat; 
}

void SKIKBO::freeMem(VarOccMap& vomtl1 , VarOccMap& vomtl2) const
{
  CALL("SKIKBO::freeMem");

  VarOccMap::Iterator it1(vomtl1);
  while(it1.hasNext()){
    DArray<DArray<unsigned>*>* arr = it1.next();
    delete arr;
  }

  VarOccMap::Iterator it2(vomtl2);
  while(it2.hasNext()){
    DArray<DArray<unsigned>*>* arr = it2.next();
    delete arr;
  }
}

bool SKIKBO::canBeMatched(DArray<unsigned>* redLengths1, DArray<unsigned>* redLengths2) const
{
  CALL("SKIKBO::canBeMatched");

  for(unsigned i = 0; i < redLengths1->size(); i++){
    if(i < redLengths2->size()){
      if((*redLengths1)[i] > (*redLengths2)[i]){
        return false;
      } 
    } else if((*redLengths1)[i] > 0){
      return false;
    }
  }
  return true;
}

bool SKIKBO::bpm(unsigned n, DArray<DArray<bool>>& bpGraph, int u, 
         DArray<bool>& seen , DArray<int>& matchR) const
{ 
  CALL("SKIKBO::bpm");

  for (int v = 0; v < n; v++) 
  { 
    if (bpGraph[u][v] && !seen[v]) 
    { 
      seen[v] = true;  
      if (matchR[v] < 0 || bpm(n, bpGraph, matchR[v], seen, matchR)) 
      { 
        matchR[v] = u; 
        return true; 
      } 
    } 
  } 
  return false; 
} 
  
bool SKIKBO::totalBMP(unsigned m, unsigned n, DArray<DArray<bool>>& bpGraph) const
{ 
  CALL("SKIKBO::totalBMP");
  
  DArray<int> matchR;
  matchR.init(n, -1);

  for (int u = 0; u < m; u++) 
  { 
    DArray<bool> seen;
    seen.init(n, 0);

    if (!bpm(n, bpGraph, u, seen, matchR)){return false;} 
  } 
  return true; 
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
  return (unsigned)tRedLen;
}


Ordering::Result SKIKBO::compare(TermList tl1, TermList tl2) const
{
  CALL("SKIKBO::compare(TermList)");

  //cout << "comparing " + tl1.toString() << endl;
  //cout << "with " + tl2.toString() << endl;

  if(tl1==tl2) {
    return EQUAL;
  }

  if(tl1.containsSubterm(tl2)){
    return GREATER;
  }

  if(tl2.containsSubterm(tl1)){
    return LESS;
  }

  VarCondRes varCond = compareVariables(tl1, tl2);

  if(varCond == INCOMP){ return INCOMPARABLE; }
  
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

  ApplicativeArgsIt* aat1 = new ApplicativeArgsIt(tl1);
  ApplicativeArgsIt* aat2 = new ApplicativeArgsIt(tl2);

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
  /*if(res == LESS){ cout << tl1.toString() + " < " + tl2.toString(); }
  if(res == GREATER){ cout << tl1.toString() + " > " + tl2.toString(); }
  if(res == INCOMPARABLE){ cout << tl1.toString() + " <> " + tl2.toString(); }*/
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

{  CALL("SKIKBO::maximumReductionLength");  
       
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
    if(!AH::isComb(head) || AH::isUnderApplied(head, args.size())){
      while(!args.isEmpty()){
        addToEvaluate(args.pop());
      }
    } else {
      if(AH::getComb(head) == Signature::K_COMB){
        addToEvaluate(args[args.size()-2]); 
      }      
      addToEvaluate(reduce(args, head));
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
