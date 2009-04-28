/**
 * @file EGSubstitution.cpp
 * Implements polynomial modification of the Robinson unification algorithm.
 */

#include "../Lib/Environment.hpp"

#include "../Lib/Hash.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/DHMultiset.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/SkipList.hpp"
#include "../Lib/Int.hpp"

#include "Term.hpp"
#include "Clause.hpp"
#include "Renaming.hpp"

#include "../Indexing/TermSharing.hpp"

#include "EGSubstitution.hpp"

#if VDEBUG
#include "../Test/Output.hpp"
#include "../Lib/Int.hpp"
#include "../Debug/Tracer.hpp"
#include <string>
#include <iostream>
using namespace Debug;
#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

const int EGSubstitution::RESERVED_INDEX=-4;
const int EGSubstitution::AUX_INDEX=-3;
const int EGSubstitution::SPECIAL_INDEX=-2;
const int EGSubstitution::UNBOUND_INDEX=-1;

const EGSubstitution::TermSpec EGSubstitution::TS_DONE(TermList(1,false),RESERVED_INDEX);
const EGSubstitution::TermSpec EGSubstitution::TS_LOOP(TermList(2,false),RESERVED_INDEX);
const EGSubstitution::TermSpec EGSubstitution::TS_NIL(TermList(3,false),RESERVED_INDEX);

/**
 * Unify @b t1 and @b t2, and return true iff it was successful.
 */
bool EGSubstitution::unify(TermList t1,int index1, TermList t2, int index2)
{
  CALL("EGSubstitution::unify/4");
  return unify(TermSpec(t1,index1), TermSpec(t2,index2));
}

/**
 * Unify arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
bool EGSubstitution::unifyArgs(Term* t1,int index1, Term* t2, int index2)
{
  CALL("EGSubstitution::unifyArgs");
  ASS_EQ(t1->functor(),t2->functor());

  TermList t1TL(t1);
  TermList t2TL(t2);
  return unify(TermSpec(t1TL,index1), TermSpec(t2TL,index2));
}

bool EGSubstitution::match(TermList base,int baseIndex,
	TermList instance, int instanceIndex)
{
  CALL("EGSubstitution::match(TermList...)");
  return match(TermSpec(base,baseIndex), TermSpec(instance,instanceIndex));
}
/**
 * Match arguments of @b t1 and @b t2, and return true iff it was successful.
 *
 * @b t1 and @b t2 can be either terms or literals.
 */
bool EGSubstitution::matchArgs(Term* base,int baseIndex,
	Term* instance, int instanceIndex)
{
  CALL("EGSubstitution::match(Literal*...)");
  ASS_EQ(base->functor(),instance->functor());

  TermList baseTL(base);
  TermList instanceTL(instance);
  return match(TermSpec(baseTL,baseIndex), TermSpec(instanceTL,instanceIndex));
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
void EGSubstitution::denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex)
{
  CALL("EGSubstitution::denormalize");
  ASSERT_VALID(normalizer);

  VirtualIterator<Renaming::Item> nit=normalizer.items();
  while(nit.hasNext()) {
    Renaming::Item itm=nit.next();
    VarSpec normal(itm.second, normalIndex);
    VarSpec denormalized(itm.first, denormalizedIndex);
    ASS(!_bank.find(denormalized));
    bindVar(denormalized,normal);
  }
}

void EGSubstitution::storeForBacktrack(VarSpec v)
{
  if(bdIsRecording()) {
    BindingBacktrackObject* bo;
    TermSpec trm;
    if(!_bank.find(v,trm)) {
      bo=new BindingBacktrackObject(this, v);
    } else {
      if(trm.index==RESERVED_INDEX) {
	bo=0;
      } else {
	bo=new BindingBacktrackObject(this, v, trm);
      }
    }
    if(bo) {
      bdAdd(bo);
    }
  }
}

EGSubstitution::TermSpec EGSubstitution::parent(VarSpec v) const
{
  CALL("EGSubstitution::parent");

  TermSpec binding;
  bool found=_bank.find(v,binding);
  if(!found || binding.index==UNBOUND_INDEX) {
    return TS_NIL;
  }
  return binding;
}

void EGSubstitution::setParent(VarSpec v, TermSpec t, bool canCauseLoop)
{
  CALL("EGSubstitution::setParent");

  storeForBacktrack(v);
  if(canCauseLoop && t.index!=RESERVED_INDEX) {
    markChanged(v);
  }
  _bank.set(v,t);
}

bool EGSubstitution::isRoot(VarSpec v) const
{
  CALL("EGSubstitution::isRoot");

  TermSpec p=parent(v);
  //root variable points either to a non-variable term or nowhere.
  return p==TS_NIL || !p.isVar();
}

EGSubstitution::VarSpec EGSubstitution::root(VarSpec v, VarStack& path)
{
  CALL("EGSubstitution::root");

  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX || !binding.isVar()) {
      return v;
    }
    path.push(v);
    setParent(v,TS_DONE);
    v=getVarSpec(binding);
  }
}

EGSubstitution::VarSpec EGSubstitution::getRootAndCollapse(VarSpec v)
{
  CALL("EGSubstitution::root");

  static VarStack path(8);
  ASS(path.isEmpty());
  VarSpec prev;
  bool first=true;

  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX || !binding.isVar()) {
      break;
    }
    if(!first) {
      path.push(prev);
      setParent(prev,TS_DONE);
    } else {
      first=false;
    }

    prev=v;
    v=getVarSpec(binding);
    if(v==prev) {
      break;
    }
  }

  collapse(path,v,false);
  return v;
}

EGSubstitution::VarSpec EGSubstitution::rootWithoutCollapsing(VarSpec v) const
{
  CALL("EGSubstitution::root");

  //the implementation below could loop indefinitely
  NOT_IMPLEMENTED;

  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX || !binding.isVar()) {
      return v;
    }
    v=getVarSpec(binding);
  }
}

void EGSubstitution::collapse(VarStack& path, VarSpec v, bool canCauseLoop)
{
  CALL("EGSubstitution::collapse");

  TermSpec tgt(v);
  while(path.isNonEmpty()) {
    setParent(path.pop(), tgt, canCauseLoop);
  }
}

void EGSubstitution::markChanged(VarSpec v)
{
  CALL("EGSubstitution::markChanged");

  unsigned* pts;
  _tStamps.getValuePtr(v,pts,0);
  ASS_LE(*pts,_currTimeStamp);

  if(*pts!=_currTimeStamp) {
    *pts=_currTimeStamp;
    _unchecked.push(v);
  }
}

void EGSubstitution::nextTimeStamp()
{
  CALL("EGSubstitution::nextTimeStamp");

  _currTimeStamp++;
  ASS_NEQ(_currTimeStamp,0); //check overflow
}


bool EGSubstitution::isUnbound(VarSpec v) const
{
  CALL("EGSubstitution::isUnbound");

  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX) {
      return true;
    } else if(binding.term.isTerm()) {
      return false;
    }
    v=getVarSpec(binding);
  }
}

/**
 * If special variable @b specialVar is bound to a proper term,
 * return a term, thjat has the same top functor. Otherwise
 * return an arbitrary variable.
 */
TermList EGSubstitution::getSpecialVarTop(unsigned specialVar)
{
  VarSpec u(specialVar, SPECIAL_INDEX);
  VarSpec v=getRootAndCollapse(u);
  TermSpec vPar=parent(v);
  if(vPar.isVar() || vPar==TS_NIL) {
    return TermList(0,false);
  } else {
    return vPar.term;
  }
}

/**
 * If @b t is a non-variable, return @t. Else, if @b t is a variable bound to
 * a non-variable term, return the term. Otherwise, return the root variable
 * to which @b t belongs.
 */
EGSubstitution::TermSpec EGSubstitution::derefBound(TermSpec t) const
{
  CALL("EGSubstitution::derefBound");
  if(t.term.isTerm()) {
    return t;
  }
  VarSpec v=getVarSpec(t);
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX) {
      return TermSpec(v);
    } else if(binding.term.isTerm()) {
      return binding;
    }
    v=getVarSpec(binding);
  }
}

EGSubstitution::TermSpec EGSubstitution::deref(VarSpec v) const
{
  CALL("EGSubstitution::deref");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found) {
      binding.index=UNBOUND_INDEX;
      binding.term.makeVar(_nextUnboundAvailable++);
      const_cast<EGSubstitution&>(*this).bind(v,binding);
      return binding;
    } else if(binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      return binding;
    }
    v=getVarSpec(binding);
  }
}

void EGSubstitution::bind(const VarSpec& v, const TermSpec& b)
{
  CALL("EGSubstitution::bind");
  ASSERT_VALID(b.term);

  //Aux terms don't contain special variables, ergo
  //should be shared.
  ASS(!b.term.isTerm() || b.index!=AUX_INDEX || b.term.term()->shared());
  ASS_NEQ(v.index, UNBOUND_INDEX);

  storeForBacktrack(v);
  _bank.set(v,b);
}

void EGSubstitution::bindVar(const VarSpec& var, const VarSpec& to)
{
  CALL("EGSubstitution::bindVar");
  ASS_NEQ(var,to);

  bind(var,TermSpec(to));
}


void EGSubstitution::swap(TermSpec& ts1, TermSpec& ts2)
{
  TermSpec aux=ts1;
  ts1=ts2;
  ts2=aux;
}


bool EGSubstitution::occursCheck(VarSpec var)
{
  CALL("EGSubstitution::occursCheck");

  static VarStack pathStack(8);
  ASS(pathStack.isEmpty());

  static Stack<pair<VarSpec,TermSpec> > checkingStack(16);
  ASS(checkingStack.isEmpty());

  checkingStack.push(make_pair(var,TS_LOOP));

  bool fail=false;

  while(checkingStack.isNonEmpty()) {
    VarSpec u=checkingStack.top().first;
    TermSpec tgt=checkingStack.pop().second;
    if(tgt!=TS_LOOP) {
      ASS(isRoot(u));
      _bank.set(u,tgt);
//      setParent(u, tgt, false);
      continue;
    }

    VarSpec v=getRootAndCollapse(u);
    TermSpec vPar=parent(v);

    if(vPar==TS_LOOP) {
      fail=true;
      break;
    }
    if(vPar.term.isVar()) {
      ASS_NEQ(vPar,TS_DONE);
      //vPar.term.isVar() is true also for TS_NIL.

      //The equivalence class doesn't contain a non-variable term.
      continue;
    }
    ASS_NEQ(vPar.index, RESERVED_INDEX);

    Term* trm=vPar.term.term();
    if(trm->shared() && trm->ground()) {
      continue;
    }

    unsigned* pts;
    _tStamps.getValuePtr(v,pts,0);
    ASS_LE(*pts,_currTimeStamp);
    if(*pts==_currTimeStamp) {
      continue;
    }
    *pts=_currTimeStamp;

    checkingStack.push(make_pair(v,vPar));
    _bank.set(v,TS_LOOP);
//    setParent(v, TS_LOOP);

    ASS(vPar.term.isTerm());
    Term::VariableIterator vit(vPar.term.term());
    while(vit.hasNext()) {
      VarSpec innVar=getVarSpec(vit.next(), vPar.index);
      if(parent(innVar)==TS_NIL) {
	continue;
      }
      checkingStack.push(make_pair(innVar,TS_LOOP));
    }
  }

  //undo all TS_LOOP marks we've set
  while(checkingStack.isNonEmpty()) {
    VarSpec u=checkingStack.top().first;
    TermSpec tgt=checkingStack.pop().second;
    if(tgt!=TS_LOOP) {
      ASS(isRoot(u));
      _bank.set(u,tgt);
    }
  }

  return !fail;
}

void EGSubstitution::varUnify(VarSpec u, TermSpec t, Stack<TTPair>& toDo)
{
  CALL("EGSubstitution::varUnify");

  static VarStack pathStack(8);
  ASS(pathStack.isEmpty());

  if(parent(u)==TS_NIL) {
    setParent(u,t);
  } else if(!t.isVar()) {
    VarSpec v=root(u, pathStack);
    collapse(pathStack, v, false);
    TermSpec vPar=parent(v);
    if(vPar==TS_NIL) {
      setParent(v,t);
    } else {
      recurUnify(v, vPar, t, toDo);
    }
  } else {
    VarSpec tVar=getVarSpec(t);
    TermSpec tPar=parent(tVar);
    if(tPar==TS_NIL) {
      setParent(tVar,TermSpec(u));
    } else {
      VarSpec v=root(u, pathStack);
      TermSpec vPar=parent(v);
      if(vPar==TS_NIL || vPar==TS_DONE) {
	pathStack.push(v);
	collapse(pathStack, v, false);
      } else {
	VarSpec w=root(tVar, pathStack);
	if(v==w) {
	  collapse(pathStack, v, false);
	} else {
	  TermSpec wPar=parent(w);
	  pathStack.push(w);
	  collapse(pathStack, v);
	  if(wPar!=TS_NIL && wPar!=TS_DONE) {
	    recurUnify(v, vPar, wPar, toDo);
	  }
	}
      }

    }
  }
}

void EGSubstitution::recurUnify(VarSpec v, TermSpec y, TermSpec t, Stack<TTPair>& toDo)
{
  CALL("EGSubstitution::recurUnify");
  ASS(!y.isVar());
  ASS(!t.isVar());
  ASS_NEQ(y.index, RESERVED_INDEX);
  ASS_NEQ(t.index, RESERVED_INDEX);

  toDo.push(make_pair(TermSpec(v),y));
  toDo.push(make_pair(y,t));
  toDo.push(make_pair(TermSpec(v),TS_LOOP));
}

bool EGSubstitution::unify(TermSpec t1, TermSpec t2)
{
  CALL("EGSubstitution::unify/2");
  ASS(_unchecked.isEmpty());

//  cout<<"------------------------------\n";
//  cout<<"unif of "<<t1<<" and "<<t2<<endl;
//  cout<<"------------------------------\n";
//  cout<<toString(false);

  if(t1.sameTermContent(t2)) {
    return true;
  }

  nextTimeStamp();

  bool fail=false;
  BacktrackData localBD;
  bdRecord(localBD);

  //Stack that helps to avoid recursive calls. TermSpec pairs
  //can either be both proper terms, in which case they should be
  //unified, or a variable and proper term, while variable's
  //parent is the TS_LOOP constant. In this case variable should
  //be bound to the term.
  static Stack<TTPair> toDo(64);
  ASS(toDo.isEmpty());

  if(t1.isVar()) {
    varUnify(getVarSpec(t1),t2,toDo);
  } else if(t2.isVar()) {
    varUnify(getVarSpec(t2),t1,toDo);
  } else {
    toDo.push(make_pair(t1,t2));
  }

  static Stack<TermList*> subterms(64);
  ASS(subterms.isEmpty());
  while(toDo.isNonEmpty()) {
    t1=toDo.top().first;
    t2=toDo.pop().second;

    if(t1.isVar()) {
      VarSpec v=getVarSpec(t1);
      ASS(t2==TS_LOOP || parent(v)==TS_LOOP);
      setParent(v,t2);
      continue;
    }

    if(t1==TS_LOOP || t2==TS_LOOP) {
      fail=true;
      break;
    }

    ASS(!t2.isVar());
    ASS_NEQ(t1.index, RESERVED_INDEX);
    ASS_NEQ(t2.index, RESERVED_INDEX);

    if(t1.sameTermContent(t2)) {
      continue;
    }

    TermList* ss=&t1.term;
    TermList* tt=&t2.term;

    for (;;) {
      TermSpec tsss(*ss,t1.index);
      TermSpec tstt(*tt,t2.index);

      if (!tsss.sameTermContent(tstt) && TermList::sameTopFunctor(*ss,*tt)) {
	ASS(ss->isTerm() && tt->isTerm());

	Term* s = ss->term();
	Term* t = tt->term();
	ASS_G(s->arity(), 0);
	ASS_EQ(s->functor(), t->functor());

	ss = s->args();
	tt = t->args();
	if (! ss->next()->isEmpty()) {
	  subterms.push(ss->next());
	  subterms.push(tt->next());
	}
      } else {
	if (! TermList::sameTopFunctor(*ss,*tt)) {
	  if(ss->isVar()) {
	    varUnify(getVarSpec(tsss), tstt, toDo);
	  } else if(tt->isVar()) {
	    varUnify(getVarSpec(tstt), tsss, toDo);
	  } else {
	    fail=true;
	    break;
	  }
	}

	if (subterms.isEmpty()) {
	  break;
	}
	tt = subterms.pop();
	ss = subterms.pop();
	if (! ss->next()->isEmpty()) {
	  subterms.push(ss->next());
	  subterms.push(tt->next());
	}
      }
    }
    if(fail) {
      break;
    }
  }

  if(fail) {
    subterms.reset();
    toDo.reset();
  } else {
    nextTimeStamp();

    while(_unchecked.isNonEmpty()) {
      if(!occursCheck(_unchecked.pop())) {
	fail=true;
	break;
      }
    }
  }
  _unchecked.reset();

  bdDone();

//  cout<<"------------------------------\n";
//  cout<<toString(false);

  if(fail) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }

//  cout<<"------------------------------\n";
//  cout<<(fail?" fail\n":" OK\n");
//  cout<<"------------------------------\n";
//  cout<<toString(false)<<endl;

  //Now there shouldn't be any variables bound to TermSpec with
  //index==RESERVED_INDEX in _bank.
  return !fail;
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
bool EGSubstitution::match(TermSpec base, TermSpec instance)
{
  CALL("EGSubstitution::match(TermSpec...)");

  if(base.sameTermContent(instance)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  static Stack<TermList*> subterms(64);
  ASS(subterms.isEmpty());

  TermList* bt=&base.term;
  TermList* it=&instance.term;

  TermSpec binding1;
  TermSpec binding2;

  for (;;) {
    TermSpec bts(*bt,base.index);
    TermSpec its(*it,instance.index);

    if (!bts.sameTermContent(its) && TermList::sameTopFunctor(bts.term,its.term)) {
      Term* s = bts.term.term();
      Term* t = its.term.term();
      ASS(s->arity() > 0);

      bt = s->args();
      it = t->args();
    } else {
      if (! TermList::sameTopFunctor(bts.term,its.term)) {
	if(bts.term.isSpecialVar()) {
	  VarSpec bvs(bts.term.var(), SPECIAL_INDEX);
	  if(_bank.find(bvs, binding1)) {
	    ASS_EQ(binding1.index, base.index);
	    bt=&binding1.term;
	    continue;
	  } else {
	    bind(bvs,its);
	  }
	} else if(its.term.isSpecialVar()) {
	  VarSpec ivs(its.term.var(), SPECIAL_INDEX);
	  if(_bank.find(ivs, binding2)) {
	    ASS_EQ(binding2.index, instance.index);
	    it=&binding2.term;
	    continue;
	  } else {
	    bind(ivs,bts);
	  }
	} else if(bts.term.isOrdinaryVar()) {
	  VarSpec bvs(bts.term.var(), bts.index);
	  if(_bank.find(bvs, binding1)) {
	    ASS_EQ(binding1.index, instance.index);
	    if(!TermList::equals(binding1.term, its.term))
	    {
	      mismatch=true;
	      break;
	    }
	  } else {
	    bind(bvs,its);
	  }
	} else {
	  mismatch=true;
	  break;
	}
      }

      if (subterms.isEmpty()) {
	break;
      }
      bt = subterms.pop();
      it = subterms.pop();
    }
    if (!bt->next()->isEmpty()) {
      subterms.push(it->next());
      subterms.push(bt->next());
    }
  }

  bdDone();

  subterms.reset();


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


Literal* EGSubstitution::apply(Literal* lit, int index) const
{
  CALL("EGSubstitution::apply(Literal*...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    ts[i++]=apply(*args,index);
  }
  return Literal::create(lit,ts.array());
}

TermList EGSubstitution::apply(TermList trm, int index) const
{
  CALL("EGSubstitution::apply(TermList...)");

  static Stack<TermList*> toDo(8);
  static Stack<int> toDoIndex(8);
  static Stack<Term*> terms(8);
  static Stack<VarSpec> termRefVars(8);
  static Stack<TermList> args(8);
  static DHMap<VarSpec, TermList, VarSpec::Hash1, VarSpec::Hash2> known;

  //is inserted into termRefVars, if respective
  //term in terms isn't referenced by any variable
  const VarSpec nilVS(-1,0);

  toDo.push(&trm);
  toDoIndex.push(index);

  while(!toDo.isEmpty()) {
    TermList* tt=toDo.pop();
    index=toDoIndex.pop();
    if(tt->isEmpty()) {
      Term* orig=terms.pop();
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());
      TermList constructed;
      constructed.setTerm(Term::create(orig,argLst));
      args.push(constructed);

      VarSpec ref=termRefVars.pop();
      if(ref!=nilVS) {
	ALWAYS(known.insert(ref,constructed));
      }
      continue;
    } else {
      //if tt==&trm, we're dealing with the top
      //term, for which the next() is undefined
      if(tt!=&trm) {
	toDo.push(tt->next());
	toDoIndex.push(index);
      }
    }

    TermSpec ts(*tt,index);

    VarSpec vs;
    if(ts.term.isVar()) {
      vs=rootWithoutCollapsing(getVarSpec(ts));

      TermList found;
      if(known.find(vs, found)) {
	args.push(found);
	continue;
      }

      ts=deref(vs);
      if(ts.term.isVar()) {
	ASS(ts.index==UNBOUND_INDEX);
	args.push(ts.term);
	continue;
      }
    } else {
      vs=nilVS;
    }
    Term* t=ts.term.term();
    if(t->shared() && t->ground()) {
      args.push(ts.term);
      continue;
    }
    terms.push(t);
    termRefVars.push(vs);

    toDo.push(t->args());
    toDoIndex.push(ts.index);
  }
  ASS(toDo.isEmpty() && toDoIndex.isEmpty() && terms.isEmpty() && args.length()==1);
  known.reset();
  return args.pop();
}


#if VDEBUG
string EGSubstitution::toString(bool deref) const
{
  CALL("EGSubstitution::toString");
  string res;
  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec v;
    TermSpec binding;
    bit.next(v,binding);
    TermList tl;
    if(v.index==SPECIAL_INDEX) {
      res+="S"+Int::toString(v.var)+" -> ";
      tl.makeSpecialVar(v.var);
    } else {
      res+="X"+Int::toString(v.var)+"/"+Int::toString(v.index)+ " -> ";
      tl.makeVar(v.var);
    }
    if(deref) {
      tl=apply(tl, v.index);
      res+=Test::Output::singleTermListToString(tl)+"\n";
    } else {
      res+=Test::Output::singleTermListToString(binding.term)+"/"+Int::toString(binding.index)+"\n";
    }

  }
  return res;
}

std::string EGSubstitution::VarSpec::toString() const
{
  if(index==SPECIAL_INDEX) {
    return "S"+Int::toString(var);
  } else {
    return "X"+Int::toString(var)+"/"+Int::toString(index);
  }
}

string EGSubstitution::TermSpec::toString() const
{
  return Test::Output::singleTermListToString(term)+"/"+Int::toString(index);
}

ostream& operator<< (ostream& out, EGSubstitution::VarSpec vs )
{
  return out<<vs.toString();
}

ostream& operator<< (ostream& out, EGSubstitution::TermSpec ts )
{
  return out<<ts.toString();
}

#endif

/**
 * First hash function for DHMap.
 */
unsigned EGSubstitution::VarSpec::Hash1::hash(VarSpec& o, int capacity)
{
//  return o.var + o.index*(capacity>>1) + (o.index>>1)*(capacity>>3);
//  return o.var^(o.var/capacity) + o.index*(capacity>>1) + (o.index>bv>2)*(capacity>>3);
//This might work better

  int res=(o.var%(capacity<<1) - capacity);
  if(res<0)
    //this turns x into -x-1
    res = ~res;
  if(o.index&1)
    return static_cast<unsigned>(-res+capacity-o.index);
  else
    return static_cast<unsigned>(res);
}

/**
 * Second hash function for DHMap. It just uses the hash function from Lib::Hash
 */
unsigned EGSubstitution::VarSpec::Hash2::hash(VarSpec& o)
{
  return Lib::Hash::hash(reinterpret_cast<const unsigned char*>(&o), sizeof(VarSpec));
//  return o.var+o.index;
}

}
