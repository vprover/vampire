/**
 * @file MMSubstitution.cpp
 * Implements Martelli and Montanari unification.
 */

#include "../Lib/Hash.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/DHMultiset.hpp"

#include "../Kernel/Renaming.hpp"
#include "../Indexing/TermSharing.hpp"

#include "Term.hpp"
#include "MMSubstitution.hpp"

#ifdef VDEBUG
#include "../Test/Output.hpp"
#include "../Lib/Int.hpp"
#include <string>
#include <iostream>
#endif


using namespace std;
using namespace Lib;
using namespace Kernel;

bool MMSubstitution::unify(TermList t1,int index1, TermList t2, int index2)
{
  CALL("MMSubstitution::unify/4");
  return unify(TermSpec(t1,index1), TermSpec(t2,index2));
}

void MMSubstitution::denormalize(const Renaming& normalizer, int normalIndex, int denormalizedIndex)
{
  CALL("MMSubstitution::denormalize");
  ASSERT_VALID(normalizer);

  static Stack<unsigned> normalVars(8);

  Renaming denormalizer;
  Renaming::inverse(normalizer, denormalizer);

  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec vs=bit.nextKey();
    if(vs.index==normalIndex) {
      normalVars.push(vs.var);
    }
  }

  //cout<<"-------"<<endl<<"preNorm:"<<endl<<toString(false);

  while(!normalVars.isEmpty()) {
    VarSpec normal(normalVars.pop(), normalIndex);
    VarSpec denormalized(denormalizer.apply(normal.var), denormalizedIndex);
    ASS(!_bank.find(denormalized));
    bindVar(denormalized,normal);
  }
  //cout<<"postNorm:"<<endl<<toString(false);
}

bool MMSubstitution::isUnbound(VarSpec v) const
{
  CALL("MMSubstitution::isUnbound");
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
 * If @b t is a non-variable, return @t. Else, if @b t is a variable bound to
 * a non-variable term, return the term. Otherwise, return the root variable
 * to which @b t belongs.
 */
MMSubstitution::TermSpec MMSubstitution::derefBound(TermSpec t) const
{
  CALL("MMSubstitution::derefBound");
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

MMSubstitution::TermSpec MMSubstitution::deref(VarSpec v) const
{
  CALL("MMSubstitution::deref");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found) {
      binding.index=UNBOUND_INDEX;
      binding.term.makeVar(_nextUnboundAvailable++);
      const_cast<MMSubstitution&>(*this).bind(v,binding);
      return binding;
    } else if(binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      return binding;
    }
    v=getVarSpec(binding);
  }
}

void MMSubstitution::bind(const VarSpec& v, const TermSpec& b)
{
  CALL("MMSubstitution::bind");

  if(bdIsRecording()) {
    bdAdd(new BindingBacktrackObject(this, v));
  }
  _bank.set(v,b);
}

void MMSubstitution::bindVar(const VarSpec& var, const VarSpec& to)
{
  CALL("MMSubstitution::bindVar");
  TermList tl;
  tl.makeVar(to.var);
  bind(var,TermSpec(tl,to.index));
}

MMSubstitution::VarSpec MMSubstitution::root(VarSpec v) const
{
  CALL("MMSubstitution::root");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found || binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      return v;
    }
    v=getVarSpec(binding);
  }
}

void MMSubstitution::makeEqual(VarSpec v1, VarSpec v2, TermSpec target)
{
  CALL("MMSubstitution::makeEqual");

  v1=root(v1);
  v2=root(v2);

  if(Random::getBit()) {
    bindVar(v1,v2);
    bind(v2,target);
  } else {
    bindVar(v2,v1);
    bind(v1,target);
  }
}

void MMSubstitution::unifyUnbound(VarSpec v, TermSpec ts)
{
  CALL("MMSubstitution::makeEqual");

  v=root(v);

  ASS(isUnbound(v));

  if(ts.isVar()) {
    VarSpec v2=getVarSpec(ts);
    makeEqual(v, v2, deref(v2));
  } else {
    bind(v,ts);
  }
}


void MMSubstitution::swap(TermSpec& ts1, TermSpec& ts2)
{
  TermSpec aux=ts1;
  ts1=ts2;
  ts2=aux;
}


bool MMSubstitution::handleDifferentTops(TermSpec t1, TermSpec t2,
	Stack<TTPair>& toDo, TermList* ct)
{
  if(t1.isVar()) {
    VarSpec v1=getVarSpec(t1);
    if(ct) {
      VarSpec ctVar=getAuxVar(v1);
      ct->makeVar(ctVar.var);
    }
    if(isUnbound(v1)) {
      unifyUnbound(v1,t2);
    } else if(t2.isVar() && isUnbound(getVarSpec(t2))) {
      unifyUnbound(getVarSpec(t2),t1);
    } else {
      toDo.push(TTPair(t1,t2));
    }
  } else if(t2.isVar()) {
    VarSpec v2=getVarSpec(t2);
    if(ct) {
      VarSpec ctVar=getAuxVar(v2);
      ct->makeVar(ctVar.index);
    }
    if(isUnbound(v2)) {
      unifyUnbound(v2,t1);
    } else {
      toDo.push(TTPair(t2,t1));
    }
  } else {
    //tops are different and neither of them is variable, so we can't unify them
    ASS(t1.term.isTerm() && t2.term.isTerm() &&
	    t1.term.term()->functor()!=t2.term.term()->functor());
    return false;
  }
  return true;
}

bool MMSubstitution::unify(TermSpec t1, TermSpec t2)
{
  CALL("MMSubstitution::unify/2");

  if(t1.sameContent(t2)) {
    return true;
  }

  bool mismatch=false;
  BacktrackData localBD;
  bdRecord(localBD);

  //toDo stack contains pairs of terms to be unified.
  //Terms in those pairs can be either complex pairs
  //or bound variables. If pair consists of one complex
  //term and one bound variable, the bound variable has
  //to be first.
  static Stack<TTPair> toDo(64);
  static Stack<TermList*> subterms(64);
  ASS(toDo.isEmpty() && subterms.isEmpty());

  if(TermList::sameTopFunctor(&t1.term,&t2.term)) {
    toDo.push(TTPair(t1,t2));
  } else {
    if(!handleDifferentTops(t1,t2,toDo,0)) {
      return false;
    }
  }


  while(!toDo.isEmpty()) {
    TTPair task=toDo.pop();
    t1=task.first;
    t2=task.second;
    ASS(!t2.isVar() || t1.isVar());

    TermSpec dt1=derefBound(t1);
    TermSpec dt2=derefBound(t2);
    ASS(!dt1.isVar() && !dt2.isVar());

    TermList* ss=&dt1.term;
    TermList* tt=&dt2.term;
    TermList* ct;

    TermSpec commonTS;
    bool buildingCommon=t1.isVar();
    if(buildingCommon) {
      commonTS.index=AUX_INDEX;
      ct=&commonTS.term;
    } else {
      ct=0;
    }


    Stack<TermList*> subterms(64);
    for (;;) {
      TermSpec tsss(*ss,t1.index);
      TermSpec tstt(*tt,t2.index);

      if (!tsss.sameContent(tstt) && TermList::sameTopFunctor(ss,tt)) {
        ASS(ss->isTerm() && tt->isTerm());

        Term* s = ss->term();
        Term* t = tt->term();
        ASS(s->arity() > 0);
        ASS(s->functor() == t->functor());

        if(ct) {
          ct->setTerm(Term::createNonShared(t));
        }

        ss = s->args();
        tt = t->args();
        ct = ct ? ct->term()->args() : 0;
        if (! ss->next()->isEmpty()) {
          subterms.push(ss->next());
          subterms.push(tt->next());
          subterms.push(ct ? ct->next() : 0);
        }
      } else {
        if (! TermList::sameTopFunctor(ss,tt)) {
          if(!handleDifferentTops(tsss,tstt,toDo,ct)) {
            mismatch=true;
            break;
          }
        } else { //ss->sameContent(tt)
          if(ct) {
            *ct=*ss;
          }
        }

        if (subterms.isEmpty()) {
          break;
        }
        ct = subterms.pop();
        tt = subterms.pop();
        ss = subterms.pop();
        if (! ss->next()->isEmpty()) {
          subterms.push(ss->next());
          subterms.push(tt->next());
          subterms.push(ct ? ct->next() : 0);
        }
      }
    }

    if(mismatch) {
      if(buildingCommon && commonTS.term.isTerm()) {
	commonTS.term.term()->destroyNonShared();
      }
      break;
    }

    if(t1.isVar()) {
      ASS(buildingCommon);
      ASS(!commonTS.isVar());
      VarSpec v1=root(getVarSpec(t1));

      Term* shared=env.sharing->insertRecurrently(commonTS.term.term());
      commonTS.term.setTerm(shared);

      if(t2.isVar()) {
	VarSpec v2=root(getVarSpec(t2));
	makeEqual(v1, v2, commonTS);
      } else {
	bind(v1, commonTS);
      }
    }
  }

  if(!mismatch) {
    mismatch=occurCheckFails();
  } else {
    subterms.reset();
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

Literal* MMSubstitution::apply(Literal* lit, int index) const
{
  CALL("MMSubstitution::apply(Literal*...)");
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

TermList MMSubstitution::apply(TermList trm, int index) const
{
  CALL("MMSubstitution::apply(TermList...)");

  static Stack<TermList*> toDo(8);
  static Stack<int> toDoIndex(8);
  static Stack<Term*> terms(8);
  static Stack<TermList> args(8);

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

    if(ts.term.isVar()) {
      ts=deref(getVarSpec(ts));
      if(ts.term.isVar()) {
	ASS(ts.index==UNBOUND_INDEX);
	args.push(ts.term);
	continue;
      }
    }
    Term* t=ts.term.term();
    if(t->shared() && t->ground()) {
      args.push(ts.term);
      continue;
    }
    terms.push(t);
    toDo.push(t->args());
    toDoIndex.push(ts.index);
  }
  ASS(toDo.isEmpty() && toDoIndex.isEmpty() && terms.isEmpty() && args.length()==1);
  return args.pop();
}

bool MMSubstitution::occurCheckFails() const
{
  CALL("MMSubstitution::occurCheckFails");

  Stack<VarSpec> maybeUnref(8);
  Stack<VarSpec> unref(8);
  DHMultiset<VarSpec,VarSpec::Hash1,VarSpec::Hash2> refCounter;

  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec vs;
    TermSpec ts;
    bit.next(vs,ts);
    if(!ts.term.isTerm()) {
      continue;
    }
    if(!refCounter.find(vs)) {
      maybeUnref.push(vs);
    }
    Term::VariableIterator vit(ts.term.term());
    while(vit.hasNext()) {
      VarSpec r=root(VarSpec(vit.next().var(),ts.index));
      refCounter.insert(r);
    }
  }
  while(!maybeUnref.isEmpty()) {
    VarSpec vs=maybeUnref.pop();
    if(!refCounter.find(vs)) {
      unref.push(vs);
    }
  }
  while(!unref.isEmpty()) {
    VarSpec v=unref.pop();
    TermSpec ts=_bank.get(v);
    ASS(ts.term.isTerm());
    Term::VariableIterator vit(ts.term.term());
    while(vit.hasNext()) {
      VarSpec r=root(VarSpec(vit.next().var(),ts.index));
      refCounter.remove(r);
      if(!refCounter.find(r)) {
	TermSpec rts;
	if(_bank.find(r, rts) && rts.term.isTerm()) {
	  unref.push(r);
	}
      }
    }
  }
  return refCounter.size()!=0;
}


#ifdef VDEBUG
string MMSubstitution::toString(bool deref) const
{
  CALL("MMSubstitution::toString");
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
#endif


/**
 * First hash function for DHMap.
 */
unsigned MMSubstitution::VarSpec::Hash1::hash(VarSpec& o, int capacity)
{
  return o.var + o.index*capacity>>1 + o.index>>1*capacity>>3;
/*//This might work better

  int res=(o.var%(capacity<<1) - capacity);
  if(res<0)
    //this turns x into -x-1
    res = ~res;
  if(o.index)
    return static_cast<unsigned>(-res+capacity-o.index);
  else
    return static_cast<unsigned>(res);*/
}

/**
 * Second hash function for DHMap. It just uses the hashFNV function from Lib::Hash
 */
unsigned MMSubstitution::VarSpec::Hash2::hash(VarSpec& o)
{
  return Lib::Hash::hashFNV(reinterpret_cast<const unsigned char*>(&o), sizeof(VarSpec));
}
