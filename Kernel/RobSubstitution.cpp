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
 * @file RobSubstitution.cpp
 * Implements polynomial modification of the Robinson unification algorithm.
 */


#include "RobSubstitution.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Output.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"

#include "Renaming.hpp"
#include "SortHelper.hpp"
#include "TermIterators.hpp"

namespace Kernel
{

using namespace Lib;


const int TermSpec::SPECIAL_INDEX=-2;
const int TermSpec::UNBOUND_INDEX=-1;

template<class TermSpecOrList, class VarBankOrInt>
void UnificationConstraintStack<TermSpecOrList, VarBankOrInt>::add(Constraint c, Option<BacktrackData&> bd)
{ 
  CALL("UnificationConstraintStack::add");

  if (bd) {
    backtrackablePush(_cont, std::move(c), *bd); 
  } else {
    _cont.push(std::move(c));
  }
}

template<class TermSpecOrList, class VarBankOrInt>
UnificationConstraint<TermSpecOrList,VarBankOrInt> 
UnificationConstraintStack<TermSpecOrList, VarBankOrInt>::pop(Option<BacktrackData&> bd)
{ 
  CALL("UnificationConstraintStack::pop");

  auto old = _cont.pop();
  if (bd) {
    bd->addClosure([this, old = old.clone()]() mutable { _cont.push(std::move(old)); });
  }
  return old;
}

template<class TermSpecOrList, class VarBankOrInt>
Recycled<Stack<Literal*>> UnificationConstraintStack<TermSpecOrList, VarBankOrInt>::literals(RobSubst& s)
{ 
  CALL("UnificationConstraintStack::literals");

  Recycled<Stack<Literal*>> out;
  out->reserve(_cont.size());
  out->loadFromIterator(literalIter(s));
  return out;
}

template<class TermSpecOrList, class VarBankOrInt>
Option<Literal*> UnificationConstraint<TermSpecOrList, VarBankOrInt>::toLiteral(RobSubst& s)
{ 
  CALL("UnificationConstraint::toLiteral");

  auto t1 = s.apply(_t1);
  auto t2 = s.apply(_t2);

  return t1 == t2 
    ? Option<Literal*>()
    : Option<Literal*>(Literal::createEquality(false, t1, t2, t1.isTerm() ? SortHelper::getResultSort(t1.term()) : SortHelper::getResultSort(t2.term())));
}

/**
 * Bind variables from @b denormalizedIndex to variables in @b normalIndex
 * in a way, that applying the substitution to a term in @b denormalizedIndex
 * would give the same result as first renaming variables and then applying
 * the substitution in @b normalIndex.
 *
 * @warning All variables, that occured in some term that was matched or unified
 * in @b normalIndex, must be also present in the @b normalizer.
 */
template<class TermSpecOrList, class VarBankOrInt>
void RobSubstitution<TermSpecOrList, VarBankOrInt>::denormalize(const Renaming& normalizer, VarBankOrInt normBank, VarBankOrInt denormBank)
{
  CALL("RobSubstitution::denormalize");

  VirtualIterator<Renaming::Item> nit=normalizer.items();
  while(nit.hasNext()) {
    Renaming::Item itm=nit.next();
    TermSpecOrList normal(itm.second, normBank);
    TermSpecOrList denormalized(itm.first, denormBank);

    if (denormBank == _outputIndex) {
      ASS(!_bank.find(normal));
      bind(normal, denormalized);
    } else {
      ASS(!_bank.find(denormalized));
      bind(denormalized,normal);
    }
  }
}

template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList, VarBankOrInt>::isUnbound(TermSpecOrList v) const
{
  CALL("RobSubstitution::isUnbound");
  ASS(v.isVar());
  
  for(;;) {
    auto binding = _bank.find(v);
    if(binding.isNone() || binding->isOutputVar()) {
      return true;
    } else if(binding->isTerm()) {
      return false;
    }
    v = binding.unwrap();
  }
}

/**
 * If special variable @b specialVar is bound to a proper term,
 * return a term, that has the same top functor. Otherwise
 * return an arbitrary variable.
 */
template<class TermSpecOrList, class VarBankOrInt>
TermList::Top 
RobSubstitution<TermSpecOrList, VarBankOrInt>::getSpecialVarTop(unsigned specialVar) const
{
  TermSpecOrList v(specialVar, true);
  for(;;) {
    auto binding = _bank.find(v);
    if(binding.isNone() || binding->isOutputVar()) {
      static TermList auxVarTerm(1,false);
      return auxVarTerm.top();
    } else if(binding->isTerm()) {
      return binding->top();
    }
    v = binding.unwrap();
  }
}

/**
 * If @b t is a non-variable, return @b t. Else, if @b t is a variable bound to
 * a non-variable term, return the term. Otherwise, return the root variable
 * to which @b t belongs.
 */
template<class TermSpecOrList, class VarBankOrInt>
TermSpecOrList RobSubstitution<TermSpecOrList, VarBankOrInt>::derefBound(TermSpecOrList const& t_) const
{
  CALL("RobSubstitution::derefBound");

  TermSpecOrList const* t = &t_;
  for(;;) {
    if (t->isTerm() || t->isOutputVar()) {
      return *t;
    } else {
      ASS(t->isVar());
      auto binding = _bank.find(*t);
      if (!binding || binding->isOutputVar()) {
        return *t;
      } else {
        t = &binding.unwrap();
      }
    }
  }
}

/**
 * If @b is bound return the root variable / term it is bound to.
 * If _outputIndex == UNBOUND_INDEX (default behaviour), return the next
 * unbound variable in the UNBOUND_INDEX. This effectively names unbound
 * variables apart from any variables in the range of bound variables.
 * If _outputIndex != UNBOUND_INDEX, (i.e. it has been set to something
 * else using setOutputIndex), the root variable must be of the
 * _outputIndex and is returned as is, otherwise we fail on an exception.
 */
template<class TermSpecOrList, class VarBankOrInt>
TermSpecOrList RobSubstitution<TermSpecOrList, VarBankOrInt>::deref(TermSpecOrList v) const
{
  CALL("RobSubstitution::deref");
  ASS(v.isVar());

  for(;;) {
    auto binding = _bank.find(v);
    if(binding.isNone()) {
      if(isDefault(_outputIndex)){
        const_cast<RobSubstitution&>(*this).bind(v, getUnboundVar());
        return _bank.get(v);
      } else {
        ASS_REP(v.bank() == _outputIndex, "variable bound index different from _outputIndex. This probably means you either called the wrong operations (e.g. unify) after using setOutputIndex, or you are trying to apply the substitution to a variable that was not bound by this substitution (e.g. by calling RobSubstitution::match or so)")        
        return v;
      }
    } else if(binding->isTerm() || binding->bank() == _outputIndex) {
      return binding.unwrap();
    }
    v = binding.unwrap();
  }
}

template<class TermSpecOrList, class VarBankOrInt>
void RobSubstitution<TermSpecOrList, VarBankOrInt>::bind(const TermSpecOrList& v, TermSpecOrList b)
{
  CALL("RobSubstitution::bind");
  ASS(v.isVar());

  //Aux terms don't contain special variables, ergo
  //should be shared.
  //ASS(!b.term.isTerm() || b.index!=AUX_INDEX || b.term.term()->shared());

  if(bdIsRecording()) {
    bdAdd(new BindingBacktrackObject(this, v));
  }
  _bank.set(v,b);
}

template<class TermSpecOrList, class VarBankOrInt>
TermSpecOrList RobSubstitution<TermSpecOrList, VarBankOrInt>::root(TermSpecOrList v) const
{
  CALL("RobSubstitution::root");
  ASS(v.isVar());

  for(;;) {
    auto binding = _bank.find(v);
    if(binding.isNone() || binding->isTerm() || binding->bank() == _outputIndex) {
      return v;
    }
    v = binding.unwrap();
  }
}

template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList, VarBankOrInt>::occurs(TermSpecOrList const& toFind_, TermSpecOrList const& ts_)
{
  ASS(toFind_.isVar());

  TermSpecOrList toFind = root(toFind_);
  TermSpecOrList ts     = derefBound(ts_);
  if(ts.isVar()) {
    return false;
  }
  typedef DHSet<TermSpecOrList> EncounterStore;
  Recycled<EncounterStore> encountered;
  Recycled<Stack<TermSpecOrList>> todo;
  todo->push(ts);

  while (todo->isNonEmpty()){
    auto ts = todo->pop();
    if (ts.isVar()) {
      TermSpecOrList tvar = root(ts);
      if(tvar == toFind) {
        return true;
      } else if(!encountered->find(tvar)) {
        TermSpecOrList dtvar = derefBound(tvar);
        if(!dtvar.isVar()) {
          encountered->insert(tvar);
          todo->push(dtvar);
        }
      }

    } else {
      for(unsigned i = 0; i < ts.term()->arity(); i++){
        todo->push(ts.nthArg(i));
      }
    }
  }

  return false;
}

template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList, VarBankOrInt>::sameTermContent(TermSpecOrList t1, TermSpecOrList t2)
{
  CALL("RobSubstitution::sameTermContent");

  bool termSameContent = t1.sameContent(t2);
  if(!termSameContent && t1.isTerm() && t1.term()->isLiteral() &&
                         t2.isTerm() && t2.term()->isLiteral()) {
    const Literal* l1=static_cast<const Literal*>(t1.term());
    const Literal* l2=static_cast<const Literal*>(t2.term());
    if(l1->functor()==l2->functor() && l1->arity()==0) {
      return true;
    }
  }
  return termSameContent;
}

bool RobSubstitutionTS::unify(TermList t1, int idx1, TermList t2, int idx2)
{
  CALL("RobSubstitution::unify/1");

  return RobSubstitution<TermSpec, int>::unify(TermSpec(t1,idx1), TermSpec(t2,idx2));
}

bool RobSubstitutionTS::match(TermList t1, int idx1, TermList t2, int idx2)
{
  CALL("RobSubstitution::match/1");

  return RobSubstitution<TermSpec, int>::match(TermSpec(t1,idx1), TermSpec(t2,idx2), idx1);
}

template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList, VarBankOrInt>::unify(TermSpecOrList t1, TermSpecOrList t2
#if VHOL
    , bool applicativeUnify
#endif  
     )
{
  CALL("RobSubstitution::unify/2");
#define DEBUG_UNIFY(lvl, ...) if (lvl < 0) DBG("unify: ", __VA_ARGS__)
  DEBUG_UNIFY(0, *this, ".unify(", t1, ",", t2, ")")


  if(sameTermContent(t1,t2)) {
    return true;
  }

  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<Constraint> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(Constraint(t1, t2));

  // Save encountered unification pairs to avoid
  // recomputing their unification
  Recycled<DHSet<Constraint>> encountered;

#if VHOL
  auto containsLooseIndex = [](TermList t){
    if(env.property->higherOrder()){
      // should never reach here from a tree
      // currently we only reach this point by a call to unifiers 
      // from condensation
      ASS(t.isVar() || t.term()->shared())
      // we don't need to dereference any bound variables
      // since we should never be binding a variable to a term that contains a loose index     
      return t.containsLooseIndex();
    }
    return false;
  };
#endif

  auto pushTodo = [&](auto pair) {
      // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
      // in order to safe memory we do ot do this for variables.
      // (Note by joe:  didn't make this decision, but just keeping the implemenntation 
      // working as before. i.e. as described in the paper "Comparing Unification 
      // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
      if (pair.lhs().isVar() && isUnbound(pair.lhs()) &&
          pair.rhs().isVar() && isUnbound(pair.rhs())) {
        toDo.push(std::move(pair));
      } else if (!encountered->find(pair)) {
        encountered->insert(pair);
        toDo.push(pair);
      }
  };

  bool mismatch=false;
  // Iteratively resolve unification pairs in toDo
  // the current pair is always in t1 and t2 with their dereferenced
  // version in dt1 and dt2
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermSpecOrList const& dt1 = derefBound(x.lhs());
    TermSpecOrList const& dt2 = derefBound(x.rhs());
    DEBUG_UNIFY(1, "next pair: ", tie(dt1, dt2))
    // If they have the same content then skip
    // (note that sameTermContent is best-effort)

    if (sameTermContent(dt1,dt2)) {
    // Deal with the case where eithe rare variables
    // Do an occurs-check and note that the variable 
    // cannot be currently bound as we already dereferenced
    } else if(dt1.isVar() && !occurs(dt1, dt2) 
#if VHOL
                          && (!applicativeUnify || !containsLooseIndex(dt2))
#endif
      ) {
      bind(dt1, dt2);

    } else if(dt2.isVar() && !occurs(dt2, dt1)
#if VHOL
                          && (!applicativeUnify || !containsLooseIndex(dt1))
#endif
      ) {
      bind(dt2, dt1);

    } else if(dt1.isTerm() && dt2.isTerm() 
           && dt1.term()->functor() == dt2.term()->functor()) {

      for (unsigned i = 0; i < dt1.term()->arity(); i++) {
        pushTodo(Constraint(dt1.nthArg(i), dt2.nthArg(i)));
      }

    } else {
      mismatch = true;
      break;
    }

    ASS(!mismatch)
  }

  if(mismatch) {
    toDo.reset();
  }

  bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(0, *this)
  return !mismatch;
}

/**
 * Matches @b instance term onto the @b base term.
 * Ordinary variables behave, as one would expect
 * during matching, but special variables aren't
 * being assigned only in the @b base term, but in
 * the instance ass well. (Special variables appear
 * only in internal terms of substitution trees and
 * this behavior allows easy instance retrieval.)
 */
template<class TermSpecOrList, class VarBankOrInt>
bool RobSubstitution<TermSpecOrList, VarBankOrInt>::match(TermSpecOrList base, TermSpecOrList instance, VarBankOrInt baseBank)
{
  CALL("RobSubstitution::match(TermSpec...)");

#define DEBUG_MATCH(lvl, ...) if (lvl < 0) DBG("match: ", __VA_ARGS__)

  if(sameTermContent(base,instance)) { return true; }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<Constraint> toDo(64);
  ASS(toDo.isEmpty());
  toDo.push(Constraint(base, instance));

  auto quickTests = [](TermList bt, TermList it){
    if(bt.isTerm() && bt.term()->shared() && it.isTerm() && it.term()->shared()){
      if(bt.term()->ground()){ return bt == it; }
      return bt.term()->weight() <= it.term()->weight();
    }
    return true;
  };

  auto canBind = [&](TermSpecOrList t)
  { return t.isVar() && t.bank() == baseBank; };

  auto dealWithSpec = [&](TermSpecOrList spec, TermSpecOrList term, bool instance){
    auto binding = _bank.find(spec);
    if(binding) {
      TermSpecOrList t = binding.unwrap();
      toDo.push(instance ? Constraint(term,t) : Constraint(t,term));
    } else {
      bind(spec, term);
    }  
  };

  auto canCompare = [](TermSpecOrList t)
  { return !t.isSpecialVar() && (t.isVar() || t.term()->shared()); };

  // Iteratively resolve matching pairs in toDo
  while (toDo.isNonEmpty()) {
    auto x = toDo.pop();
    TermSpecOrList bt = x.lhs();
    TermSpecOrList it = x.rhs();
    DEBUG_MATCH(1, "next pair: ", tie(bt, it))

    if(!quickTests(bt,it)){
      DEBUG_MATCH(1, "Rejected by quick tests")
      mismatch = true;
      break;
    }

    if(bt.isSpecialVar()) {
      dealWithSpec(bt, it, false);
    } else if(it.isSpecialVar()) {
      dealWithSpec(it, bt, true);
    } else if(canBind(bt)) {
      auto binding = _bank.find(bt);
      
      if(binding) {
        auto b = binding.unwrap();
        if(canCompare(b) && canCompare(it))
        {
          if(!TermSpecOrList::equals(b, it)){
            mismatch=true;
            break;
          }
        } else {
          toDo.push(Constraint(b,it));
        }
      } else {
#if VHOL
        if(env.property->higherOrder()){
          if(it.containsLooseIndex()){
            mismatch=true;
            break;            
          }
        }
#endif        
        bind(bt, it);
      }
    } else if (it.isVar() || bt.isVar()) {
      ASS(!canBind(it) && !canBind(bt));
      mismatch=true;
      break;      
    } else if (bt.term()->functor() == it.term()->functor()) {
      for (unsigned i = 0; i < bt.term()->arity(); i++) {
        toDo.push(Constraint(bt.nthArg(i), it.nthArg(i)));
      }
    } else {
      mismatch = true;
      break;
    }

    ASS(!mismatch)
  }

  if(mismatch) {
    toDo.reset();
  }

  bdDone();

  if(mismatch) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

  return !mismatch;
}

// AYB do we use this? Not very efficient that we are passing a stack around
// by value
template<class TermSpecOrList, class VarBankOrInt>
Stack<Literal*> RobSubstitution<TermSpecOrList, VarBankOrInt>::apply(Stack<Literal*> cl, VarBankOrInt bank) const
{
  CALL("RobSubstitution::apply(Clause*...)");
  for (unsigned i = 0; i < cl.size(); i++) {
    cl[i] = apply(cl[i], bank);
  }
  return cl;
}

template<class TermSpecOrList, class VarBankOrInt>
Literal* RobSubstitution<TermSpecOrList, VarBankOrInt>::apply(Literal* lit, VarBankOrInt bank) const
{
  CALL("RobSubstitution::apply(Literal*...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  unsigned arity = lit->arity();
  ts.ensure(arity);
  for (unsigned i = 0; i < arity; i++) {
    ts[i]=apply(getLitArg(lit,i,bank),bank);
  }
  if(lit->isTwoVarEquality()){
    TermList sort = apply(getLitSort(lit,bank),bank);
    return Literal::createEquality(lit->polarity(), ts[0], ts[1], sort);
  }

  return Literal::create(lit,ts.array());
}

template<class TermSpecOrList, class VarBankOrInt>
TermList RobSubstitution<TermSpecOrList,VarBankOrInt>::apply(TermSpecOrList trm, VarBankOrInt bank) const
{
  CALL("RobSubstitution::apply(TermList...)");

  //DBG(*this, ".apply(", trm, " " , bank ,  ")")

  auto out = evalBottomUp<TermList>(AutoDerefTerm<TermSpecOrList,VarBankOrInt>(trm, this, bank), 
      [&](auto& orig, TermList* args) -> TermList {
        //cout << "orig " << orig << endl;
        TermList tout;
        if (orig.term.isVar()) {
          ASS(!orig.term.isOutputVar())
          auto var = deref(orig.term);
          ASS(var.isVar() && var.bank() == _outputIndex);
          tout = TermList(var.var(), DEFAULT_BANK);
        } else {
          const Term* origT = orig.term.term();
          tout = TermList(origT->isSort() ? AtomicSort::create(origT->functor(), origT->arity(), args)
                                          : Term::create      (origT->functor(), origT->arity(), args));
        }
        return tout;
      });
  return out;
}

template<class TermSpecOrList, class VarBankOrInt>
size_t RobSubstitution<TermSpecOrList,VarBankOrInt>::getApplicationResultWeight(TermSpecOrList trm, VarBankOrInt bank) const
{
  CALL("RobSubstitution::getApplicationResultWeight");

  return evalBottomUp<size_t>(AutoDerefTerm<TermSpecOrList,VarBankOrInt>(trm, this, bank), 
      [](auto& orig, size_t* sizes) 
      { return orig.term.isVar() ? 1 
                                 : (1 + range(0, orig.term.term()->arity())
                                           .map([&](auto i) { return sizes[i]; })
                                           .sum()); });
}

template<class TermSpecOrList, class VarBankOrInt>
size_t RobSubstitution<TermSpecOrList, VarBankOrInt>::getApplicationResultWeight(Literal* lit, VarBankOrInt bank) const
{
  CALL("RobSubstitution::getApplicationResultWeight");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit->weight();
  }

  size_t res = 1; //the predicate symbol weight
  for (unsigned i = 0; i < lit->arity(); i++) {
    size_t argWeight = getApplicationResultWeight(getLitArg(lit,i,bank),bank);
    res += argWeight;
  }
  return res;
}


struct RobSubstitutionTL::ToRobTermList
{
  RobSubstitutionTL* operator()(RobSubstitution<TermList,VarBank>* r)
  { return static_cast<RobSubstitutionTL*>(r); }
};

struct RobSubstitutionTS::ToRobTermSpec
{
  RobSubstitutionTS* operator()(RobSubstitution<TermSpec,int>* r)
  { return static_cast<RobSubstitutionTS*>(r); }
};

/**
 * Return iterator on unifying substitutions of @b l1 and @b l2.
 *
 * For guides on use of the iterator, see the documentation of
 * RobSubstitution::AssocIterator.
 */
SubstIterator RobSubstitutionTL::unifiers(Literal* l1, Literal* l2, bool complementary)
{

  if( !Literal::headersMatch(l1,l2,complementary) ) {
    return SubstIterator::getEmpty();
  } 

  TermList s1 = l1->isEquality() ? SortHelper::getEqualityArgumentSort(l1) : TermList(0,false);
  TermList s2 = l2->isEquality() ? SortHelper::getEqualityArgumentSort(l2) : TermList(0,false);

  TermList t1 = TermList(l1);
  TermList t2 = TermList(l2);

  auto it = RobSubstitution<TermList,VarBank>::getAssocIterator(this, t1,s1,t2,s2, complementary);
  
  return pvi(getMappingIterator(it, ToRobTermList()));
}

SubstIteratorTS RobSubstitutionTS::unifiers(Literal* l1, int idx1, Literal* l2, int idx2, bool complementary)
{
  if( !Literal::headersMatch(l1,l2,complementary) ) {
    return SubstIteratorTS::getEmpty();
  }

  TermSpec s1(l1->isEquality() ? SortHelper::getEqualityArgumentSort(l1) : TermList(0,false), idx1);
  TermSpec s2(l2->isEquality() ? SortHelper::getEqualityArgumentSort(l2) : TermList(0,false), idx2);

  TermSpec t1(TermList(l1), idx1);
  TermSpec t2(TermList(l2), idx2);

  auto it = RobSubstitution<TermSpec,int>::getAssocIterator(this, t1, s1, t2, s2, complementary);

  return pvi(getMappingIterator(it, ToRobTermSpec()));  
}

template class UnificationConstraint<TermList,VarBank>;
template class UnificationConstraint<TermSpec,int>;

template class UnificationConstraintStack<TermList,VarBank>;
template class UnificationConstraintStack<TermSpec,int>;

template class RobSubstitution<TermList,VarBank>;
template class RobSubstitution<TermSpec,int>;

template<class TermSpecOrList, class VarBankOrInt>
struct RobSubstitution<TermSpecOrList,VarBankOrInt>::AssocContext
{
  AssocContext(TermSpecOrList l1, TermSpecOrList l2)
  : _l1(l1), _l2(l2) { } // only used for non-commutative, i.e. also non-equality, literals
  bool enter(RobSubst* subst)
  {
    subst->bdRecord(_bdata);
    bool res=subst->unify(_l1, _l2);
    if(!res) {
      subst->bdDone();
      ASS(_bdata.isEmpty());
    }
    return res;
  }
  void leave(RobSubst* subst)
  {
    subst->bdDone();
    _bdata.backtrack();
  }
private:
  TermSpecOrList _l1;
  TermSpecOrList _l2;
  BacktrackData _bdata;
};

/**
 * Iterator on associating[1] substitutions of two literals.
 *
 * Using this iterator requires special care, as the
 * substitution being returned is always the same object.
 * The rules for safe use are:
 * - After the iterator is created and before it's
 * destroyed, or hasNext() gives result false, the original
 * substitution is invalid.
 * - Substitution retrieved by call to the method next()
 * is valid only until the hasNext() method is called again
 * (or until the iterator is destroyed).
 * - Before each call to next(), hasNext() has to be called at
 * least once.
 *
 * There rules are quite natural, and the 3rd one is
 * required by many other iterators as well.
 *
 * Template parameter class Fn has to contain following
 * methods:
 * bool associateEqualitySorts(RobSubstitution* subst,
 *  Literal* l1, int l1Index, Literal* l2, int l2Index)
 * bool associate(RobSubstitution*, Literal* l1, int l1Index,
 * 	Literal* l2, int l2Index, bool complementary)
 * bool associate(RobSubstitution*, TermList t1, int t1Index,
 * 	TermList t2, int t2Index)
 *
 * There is supposed to be one Fn class for unification and
 * one for matching.
 *
 * [1] associate means either match or unify
 */
template<class TermSpecOrList, class VarBankOrInt>
class RobSubstitution<TermSpecOrList,VarBankOrInt>::AssocIterator: public IteratorCore<RobSubst*> {
public:
  AssocIterator(RobSubst* subst, 
    TermSpecOrList l1, 
    TermSpecOrList s1,
    TermSpecOrList l2,
    TermSpecOrList s2) :
      _subst(subst), _l1(l1), _s1(s1), _l2(l2), _s2(s2), _isEq(static_cast<const Literal*>(l1.term())->isEquality()), 
      _state(FIRST), _used(true) {
    ASS_EQ(_l1.term()->functor(), _l2.term()->functor());
    ASS(_l1.term()->commutative());
    ASS_EQ(_l1.term()->arity(), 2);
  }
  ~AssocIterator() {
    CALL("RobSubstitution::AssocIterator::~AssocIterator");
    if (_state != FINISHED && _state != FIRST) {
      backtrack(_bdataMain);
      backtrack(_bdataEqAssoc);
    }
    ASS(_bdataMain.isEmpty());
    ASS(_bdataEqAssoc.isEmpty());
  }
  bool hasNext() {
    CALL("RobSubstitution::AssocIterator::hasNext");

    if (_state == FINISHED) {
      return false;
    }
    if (!_used) {
      return true;
    }
    _used = false;

    if (_state != FIRST) {
      backtrack(_bdataMain);
    } else if (_isEq) {
      _subst->bdRecord(_bdataEqAssoc);
      if (!_subst->unify(_s1, _s2)) {
        backtrack(_bdataEqAssoc); // this might not be necessary
        _state = FINISHED;
        return false;
      }
    }

    _subst->bdRecord(_bdataMain);

    switch (_state) {
    case NEXT_STRAIGHT:
      if (_subst->unify(_l1, _l2 
#if VHOL
        , true // check for loose indices when binding
#endif
      )) {
        _state = NEXT_REVERSED;
        break;
      }
      //no break here intentionally
    case NEXT_REVERSED: {
      TermSpecOrList t11 = _l1.nthArg(0);
      TermSpecOrList t12 = _l1.nthArg(1);
      TermSpecOrList t21 = _l2.nthArg(0);
      TermSpecOrList t22 = _l2.nthArg(1);
      if (_subst->unify(t11, t22
#if VHOL
        , true
#endif
      )) {
        if (_subst->unify(t12, t21
#if VHOL          
          , true
#endif
        )) {
          _state = NEXT_CLEANUP;
          break;
        }
        //the first successful association will be undone
        //in case NEXT_CLEANUP
      }
    }
      //no break here intentionally
    case NEXT_CLEANUP:
      //undo the previous match
      backtrack(_bdataMain);
      //undo associateEqualitySorts
      backtrack(_bdataEqAssoc);
      _state = FINISHED;
      break;
    case FINISHED:
      ASSERTION_VIOLATION;
    }
    ASS(_state != FINISHED || (_bdataMain.isEmpty() && _bdataEqAssoc.isEmpty()));
    return _state != FINISHED;
  }

  RobSubst* next() {
    _used = true;
    return _subst;
  }
private:
  void backtrack(BacktrackData &_bdata) {
    CALL("RobSubstitution::AssocIterator::backtrack");

    ASS_EQ(&_bdata, &_subst->bdGet());
    _subst->bdDone();
    _bdata.backtrack();
  }

  enum State {
    FIRST = 0,
    NEXT_STRAIGHT = 0,
    NEXT_REVERSED = 1,
    NEXT_CLEANUP = 2,
    FINISHED = 3
  };

  RobSubst* _subst;
  TermSpecOrList _l1;
  TermSpecOrList _s1;  
  TermSpecOrList _l2;
  TermSpecOrList _s2;
  bool _isEq;  
  BacktrackData _bdataMain;
  BacktrackData _bdataEqAssoc;

  State _state;
  /**
   * true if the current substitution have already been
   * retrieved by the next() method, or if there isn't
   * any (hasNext() hasn't been called yet)
   */
  bool _used;
};

template<class TermSpecOrList, class VarBankOrInt>
VirtualIterator<RobSubstitution<TermSpecOrList,VarBankOrInt>*>
RobSubstitution<TermSpecOrList,VarBankOrInt>::getAssocIterator(RobSubst* subst,
    TermSpecOrList l1, TermSpecOrList s1, TermSpecOrList l2, TermSpecOrList s2, bool complementary)
{
  CALL("RobSubstitution::getAssocIterator");

  if( !l1.term()->commutative() ) {
    return pvi( getContextualIterator(getSingletonIterator(subst),
      AssocContext(l1, l2)) );
  } else {
    return vi(
      new AssocIterator(subst, l1, s1, l2, s2));
  }
}


} // namespace Kernel
