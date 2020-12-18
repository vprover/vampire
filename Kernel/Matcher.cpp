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
 * @file Matcher.cpp
 * Implements class Matcher.
 */

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"

#include "SubstHelper.hpp"

#include "Matcher.hpp"

namespace Kernel
{

namespace __MU_Aux {

class MapBinderAndApplicator
{
public:
  TermList apply(unsigned var) {
    TermList res;
    if(!_map.find(var, res)) {
      res = TermList(var, false);
    }
    return res;
  }

  bool bind(unsigned var, TermList term)
  {
    TermList* aux;
    return _map.getValuePtr(var,aux,term) || *aux==term;
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }

  void reset() { _map.reset(); }
private:
  DHMap<unsigned, TermList> _map;
};

};

/**
 * Obtain a substitution by matching @b matchedInstance onto @b matchedBase
 * and return @b resultBase after application of that substitution
 *
 * @b matchedInstance must match onto @b matchedBase.
 */
TermList MatchingUtils::getInstanceFromMatch(TermList matchedBase,
    TermList matchedInstance, TermList resultBase)
{
  CALL("MatchingUtils::getInstanceFromMatch(TermList...)");

  using namespace __MU_Aux;

  static MapBinderAndApplicator bap;
  bap.reset();

  ALWAYS( matchTerms(matchedBase, matchedInstance, bap) );
  return SubstHelper::apply(resultBase, bap);
}

Formula* MatchingUtils::getInstanceFromMatch(Literal* matchedBase,
      Literal* matchedInstance, Formula* resultBase)
{
  CALL("MatchingUtils::getInstanceFromMatch(Literal*...)");

  using namespace __MU_Aux;

  static MapBinderAndApplicator bap;
  bap.reset();

  ALWAYS( match(matchedBase, matchedInstance, false, bap) );
  return SubstHelper::apply(resultBase, bap);
}

bool MatchingUtils::isVariant(Literal* l1, Literal* l2, bool complementary)
{
  CALL("MatchingUtils::isVariant");

  if(l1->isTwoVarEquality() && l2->isTwoVarEquality()){
    TermList s1 = l1->twoVarEqSort();
    TermList s2 = l2->twoVarEqSort();
    if(s1.isVar() && s2.isVar()){}
    else if(s1.isTerm() && s2.isTerm()){
      if(s1.term()->functor() != s2.term()->functor() || 
        !haveVariantArgs(s1.term(), s2.term())){
        return false;
      }
    }else{
      return false;
    }
  }
  if(!Literal::headersMatch(l1,l2,complementary)) {
    return false;
  }
  if(!complementary && l1==l2) {
    return true;
  }
  if(l1->commutative()) {
    return haveVariantArgs(l1,l2) || haveReversedVariantArgs(l1,l2);
  } else {
    return haveVariantArgs(l1,l2);
  }
}

bool MatchingUtils::haveReversedVariantArgs(Term* l1, Term* l2)
{
  CALL("MatchingUtils::haveReversedVariantArgs");

  ASS_EQ(l1->arity(), 2);
  ASS_EQ(l2->arity(), 2);

  static DHMap<unsigned,unsigned,IdentityHash> leftToRight;
  static DHMap<unsigned,unsigned,IdentityHash> rightToLeft;
  leftToRight.reset();
  rightToLeft.reset();

  TermList s1, s2;
  bool sortUsed = false;
  if(l1->isLiteral() && static_cast<Literal*>(l1)->isTwoVarEquality())
  {
    if(l2->isLiteral() && static_cast<Literal*>(l2)->isTwoVarEquality()){
       s1 = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(l1));
       s2 = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(l2));  
       sortUsed = true;     
    } else {
      return false;
    }      
  }

  auto it1 = getConcatenatedIterator(
      vi( new DisagreementSetIterator(*l1->nthArgument(0),*l2->nthArgument(1)) ),
      vi( new DisagreementSetIterator(*l1->nthArgument(1),*l2->nthArgument(0)) ));

  VirtualIterator<pair<TermList, TermList> > dsit =
  sortUsed ? pvi(getConcatenatedIterator(vi(new DisagreementSetIterator(s1,s2)), it1)) :
             pvi(it1);
    
  while(dsit.hasNext()) {
    pair<TermList,TermList> dp=dsit.next(); //disagreement pair
    if(!dp.first.isVar() || !dp.second.isVar()) {
  return false;
    }
    unsigned left=dp.first.var();
    unsigned right=dp.second.var();
    if(right!=leftToRight.findOrInsert(left,right)) {
  return false;
    }
    if(left!=rightToLeft.findOrInsert(right,left)) {
  return false;
    }
  }
  if(leftToRight.size()!=rightToLeft.size()) {
    return false;
  }

  return true;
}

bool MatchingUtils::haveVariantArgs(Term* l1, Term* l2)
{
  CALL("MatchingUtils::haveVariantArgs");
  ASS_EQ(l1->arity(), l2->arity());

  if(l1==l2) {
    return true;
  }

  static DHMap<unsigned,unsigned,IdentityHash> leftToRight;
  static DHMap<unsigned,unsigned,IdentityHash> rightToLeft;
  leftToRight.reset();
  rightToLeft.reset();

  DisagreementSetIterator dsit(l1,l2);
  while(dsit.hasNext()) {
    pair<TermList,TermList> dp=dsit.next(); //disagreement pair
    if(!dp.first.isVar() || !dp.second.isVar()) {
  return false;
    }
    unsigned left=dp.first.var();
    unsigned right=dp.second.var();
    if(right!=leftToRight.findOrInsert(left,right)) {
  return false;
    }
    if(left!=rightToLeft.findOrInsert(right,left)) {
  return false;
    }
  }
  if(leftToRight.size()!=rightToLeft.size()) {
    return false;
  }

  return true;
}

bool MatchingUtils::matchReversedArgs(Literal* base, Literal* instance)
{
  CALL("MatchingUtils::match");
  ASS_EQ(base->arity(), 2);
  ASS_EQ(instance->arity(), 2);

  static MapBinder binder;
  binder.reset();

  bool bTwoVarEq = base->isTwoVarEquality();

  return matchTerms(*base->nthArgument(0), *instance->nthArgument(1), binder) &&
    matchTerms(*base->nthArgument(1), *instance->nthArgument(0), binder) &&
    (!bTwoVarEq || matchTerms(base->twoVarEqSort(), SortHelper::getEqualityArgumentSort(instance))
   );
}

bool MatchingUtils::matchArgs(Term* base, Term* instance)
{
  CALL("MatchingUtils::matchArgs");

  static MapBinder binder;
  binder.reset();

  return matchArgs(base, instance, binder);
}

bool MatchingUtils::matchTerms(TermList base, TermList instance)
{
  CALL("MatchingUtils::matchTerms/2");

  if(base.isTerm()) {
    if(!instance.isTerm()) {
  return false;
    }

    Term* bt=base.term();
    Term* it=instance.term();
    if(bt->functor()!=it->functor()) {
      return false;
    }
    if(bt->shared() && it->shared()) {
      if(bt->ground()) {
        return bt==it;
      }
      if(bt->weight() > it->weight()) {
        return false;
      }
    }
    ASS_G(base.term()->arity(),0);
    return matchArgs(bt, it);
  } else {
    return true;
  }
}


//////////////// FastMatchIterator ////////////////////

void OCMatchIterator::init(Literal* base, Literal* inst, bool complementary)
{
  CALL("FastMatchIterator::init");

  //TODO we don't seem to use this iterator anywhere, so 
  //have not updated to polymorphism
  if(!Literal::headersMatch(base, inst, complementary)) {
    _finished=true;
    return;
  }
  _finished=false;
  _firstMatchDone=false;
  _base=base;
  _inst=inst;
}

bool OCMatchIterator::tryNextMatch()
{
  CALL("FastMatchIterator::tryNextMatch");

  if(_finished) {
    return false;
  }
  bool success=false;
  if(!_firstMatchDone) {
    _firstMatchDone=true;
    if(!_base->commutative()) {
      _finished=true;
    }
    reset();
    success=tryDirectMatch();
  }

  if(!success && !_finished) {
    ASS(_base->commutative());
    _finished=true;

    reset();
    success=tryReversedMatch();
  }
  return success;
}

void OCMatchIterator::reset()
{
  CALL("FastMatchIterator::reset");

  _bindings.reset();
  _bound.reset();
}

bool OCMatchIterator::tryDirectMatch()
{
  CALL("FastMatchIterator::tryDirectMatch");

  bool res=MatchingUtils::matchArgs(_base, _inst, *this);
  res&=occursCheck();
  return res;
}

bool OCMatchIterator::tryReversedMatch()
{
  CALL("FastMatchIterator::tryReversedMatch");
  ASS(_base->commutative());
  ASS(_inst->commutative());

  bool res=MatchingUtils::matchTerms(*_base->nthArgument(0), *_inst->nthArgument(1), *this);
  if(res) {
    res=MatchingUtils::matchTerms(*_base->nthArgument(1), *_inst->nthArgument(0), *this);
  }
  res&=occursCheck();
  return res;
}

bool OCMatchIterator::occursCheck()
{
  CALL("OCMatchIterator::occursCheck");

  static DHMap<unsigned, OCStatus> statuses;
  static Stack<int> toDo;
  statuses.reset();
  toDo.reset();
  BoundStack::Iterator bit(_bound);
  while(bit.hasNext()) {
    unsigned var0=bit.next();
    OCStatus* pst0;
    if(!statuses.getValuePtr(var0, pst0)) {
      ASS_EQ(*pst0, CHECKED);
      continue;
    }

    *pst0=ENQUEUED;
    toDo.push(var0);

    while(toDo.isNonEmpty()) {
      int task=toDo.pop();
      if(task==-1) {
  unsigned var=toDo.pop();
  ASS_EQ(statuses.get(var), TRAVERSING);
  statuses.set(var, CHECKED);
  continue;
      }

      unsigned var=task;

      ASS_EQ(statuses.get(var), ENQUEUED);
      statuses.set(var, TRAVERSING);

      //this schedules the update of the state to CHECKED
      toDo.push(var);
      toDo.push(-1);

      TermList tgt;
      if(!_bindings.find(var, tgt)) {
  continue;
      }
//      if(tgt.isVar()) {
//  int tvar=tgt.var();
//  if(var<tvar) {
//
//  }
//  NOT_IMPLEMENTED;
//      }
//      VariableIterator vit(tgt.term());
      VariableIterator vit(tgt);
      while(vit.hasNext()) {
  unsigned chvar=vit.next().var(); //child variable number

  OCStatus* pChStatus;
  if(!statuses.getValuePtr(chvar, pChStatus)) {
    if(*pChStatus==TRAVERSING) {
      return false;
    }
    ASS_REP(*pChStatus==CHECKED||*pChStatus==ENQUEUED, *pChStatus);
    continue;
  }
  *pChStatus=ENQUEUED;

  toDo.push(chvar);
      }

    }
  }
  return true;
}

TermList OCMatchIterator::apply(unsigned var)
{
  CALL("OCMatchIterator::apply(unsigned)");

  TermList bnd;
  if(_bindings.find(var, bnd)) {
    //this may lead to an indirect recursion, but if the occurs check
    //has passed, it won't get into an infinite cycle
    return apply(bnd);
  }
  //variable is unbound
  return TermList(var, false);
}

TermList OCMatchIterator::apply(TermList t)
{
  CALL("OCMatchIterator::apply(TermList)");

  return SubstHelper::apply(t, *this);
}

Literal* OCMatchIterator::apply(Literal* lit)
{
  CALL("OCMatchIterator::apply(Literal*)");

  return SubstHelper::apply(lit, *this);
}


//////////////// Matcher ////////////////////

class Matcher::CommutativeMatchIterator
: public IteratorCore<Matcher*>
{
public:
  CommutativeMatchIterator(Matcher* matcher, Literal* base, Literal* instance)
  : _matcher(matcher), _base(base), _instance(instance),
  _state(FIRST), _used(true)
  {
    ASS(_base->commutative());
    ASS_EQ(_base->arity(), 2);
  }
  ~CommutativeMatchIterator()
  {
    if(_state!=FINISHED && _state!=FIRST) {
  backtrack();
    }
    ASS(_bdata.isEmpty());
  }
  bool hasNext()
  {
    CALL("Matcher::CommutativeMatchIterator::hasNext");

    if(_state==FINISHED) {
      return false;
    }
    if(!_used) {
      return true;
    }
    _used=false;

    if(_state!=FIRST) {
  backtrack();
    }
    _matcher->bdRecord(_bdata);

    switch(_state) {
    case NEXT_STRAIGHT:
  if(_matcher->matchArgs(_base,_instance)) {
    _state=NEXT_REVERSED;
    break;
  }
  //no break here intentionally
    case NEXT_REVERSED:
  if(_matcher->matchReversedArgs(_base,_instance)) {
    _state=NEXT_CLEANUP;
    break;
  }
    //no break here intentionally
    case NEXT_CLEANUP:
      //undo the previous match
  backtrack();

  _state=FINISHED;
  break;
    default:
  ASSERTION_VIOLATION;
    }

    ASS(_state!=FINISHED || _bdata.isEmpty());
    return _state!=FINISHED;
  }
  Matcher* next()
  {
    _used=true;
    return _matcher;
  }
private:
  void backtrack()
  {
    ASS_EQ(&_bdata,&_matcher->bdGet());
    _matcher->bdDone();
    _bdata.backtrack();
  }

  enum State {
    FIRST=0,
    NEXT_STRAIGHT=0,
    NEXT_REVERSED=1,
    NEXT_CLEANUP=2,
    FINISHED=3
  };
  Matcher* _matcher;
  Literal* _base;
  Literal* _instance;
  BacktrackData _bdata;

  State _state;
  /**
   * true if the current substitution have already been
   * retrieved by the next() method, or if there isn't
   * any (hasNext() hasn't been called yet)
   */
  bool _used;
};

struct Matcher::MatchContext
{
  MatchContext(Literal* base, Literal* instance)
  : _base(base), _instance(instance) {}
  bool enter(Matcher* matcher)
  {
    CALL("Matcher::MatchContext::enter");

    matcher->bdRecord(_bdata);
    bool res=matcher->matchArgs(_base, _instance);
    if(!res) {
      matcher->bdDone();
      ASS(_bdata.isEmpty());
    }
    return res;
  }
  void leave(Matcher* matcher)
  {
    matcher->bdDone();
    _bdata.backtrack();
  }
private:
  Literal* _base;
  Literal* _instance;
  BacktrackData _bdata;
};

MatchIterator Matcher::matches(Literal* base, Literal* instance,
    bool complementary)
{
  CALL("Matcher::matches");

  if(!Literal::headersMatch(base, instance, complementary)) {
    return MatchIterator::getEmpty();
  }
  if(base->isTwoVarEquality()){
    TermList s1 = SortHelper::getEqualityArgumentSort(base);
    TermList s2 = SortHelper::getEqualityArgumentSort(instance);
    if(!MatchingUtils::matchTerms(s1, s2)){ return MatchIterator::getEmpty(); }
  }
  if(base->arity()==0) {
    return pvi( getSingletonIterator(this) );
  }
  if( !base->commutative() ) {
    return pvi( getContextualIterator(getSingletonIterator(this),
        MatchContext(base, instance)) );
  }
  return vi( new CommutativeMatchIterator(this, base, instance) );

}

bool Matcher::matchArgs(Literal* base, Literal* instance)
{
  CALL("Matcher::matchArgs");

  BacktrackData localBD;

  bdRecord(localBD);
  bool res=MatchingUtils::matchArgs(base,instance, _binder);
  bdDone();

  if(res) {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  } else {
    localBD.backtrack();
  }
  return res;
}

bool Matcher::matchReversedArgs(Literal* base, Literal* instance)
{
  CALL("Matcher::matchReversedArgs");
  ASS(base->commutative());

  BacktrackData localBD;

  bdRecord(localBD);
  bool res=MatchingUtils::matchTerms(*base->nthArgument(0), *instance->nthArgument(1), _binder);
  if(res) {
    res=MatchingUtils::matchTerms(*base->nthArgument(1), *instance->nthArgument(0), _binder);
  }
  bdDone();

  if(res) {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  } else {
    localBD.backtrack();
  }
  return res;
}


}