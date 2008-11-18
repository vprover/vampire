/**
 * @file MMSubstitution.cpp
 * Implements Martelli and Montanari unification.
 */

#include "../Lib/Hash.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/DHMultiset.hpp"

#include "../Indexing/TermSharing.hpp"

#include "Term.hpp"
#include "MMSubstitution.hpp"

#ifdef VDEBUG
#include "../Test/Output.hpp"
#include "../Lib/Int.hpp"
#include <string>
#endif


using namespace Lib;
using namespace Kernel;

bool MMSubstitution::unify(TermList t1,int index1, TermList t2, int index2)
{
  CALL("MMSubstitution::unify");
  BacktrackData localBD;
  
  bdRecord(localBD);
  TermSpec ct=associate(TermSpec(t1,index1), TermSpec(t2,index2));
  bool failed=ct.term.isEmpty();
  if(!failed) {
    failed=occurCheckFails();
  }
  bdDone();

  if(failed) {
    localBD.backtrack();
  } else {
    if(bdIsRecording()) {
      bdCommit(localBD);
    }
    localBD.drop();
  }
  
  return !failed;
}

bool MMSubstitution::isUnbound(VarSpec v)
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

MMSubstitution::TermSpec MMSubstitution::deref(VarSpec v)
{
  CALL("MMSubstitution::deref");
  for(;;) {
    TermSpec binding;
    bool found=_bank.find(v,binding);
    if(!found) {
      binding.index=UNBOUND_INDEX;
      binding.term.makeVar(_nextUnboundAvailable++);
      bind(v, binding);
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

MMSubstitution::VarSpec MMSubstitution::root(VarSpec v)
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

void MMSubstitution::add(VarSpec v, TermSpec b)
{
  CALL("MMSubstitution::add");
  v=root(v);
  if(isUnbound(v)) {
    bind(v,b);
  } else {
    TermSpec common=associate(deref(v), b);
    bind(v,common);
  }
}

bool MMSubstitution::makeEqual(VarSpec v1, VarSpec v2)
{
  CALL("MMSubstitution::makeEqual");
  
  VarSpec r1=root(v1);
  VarSpec r2=root(v2);
  TermSpec targetVal;
  if(isUnbound(r1)) {
    targetVal=deref(r2);
  } else if(isUnbound(r2)) {
    targetVal=deref(r1);
  } else {
    targetVal=associate(deref(r1), deref(r2));
    if(targetVal.term.isEmpty()) {
      //we were unable to unify root terms of v1 and v2
      return false;
    }
  }
  if(Random::getBit()) {
    bindVar(r1,r2);
    bind(r2,targetVal);
  } else {
    bindVar(r2,r1);
    bind(r1,targetVal);
  }
  return true;
}

MMSubstitution::TermSpec MMSubstitution::associate(TermSpec t1, TermSpec t2)
{
  CALL("MMSubstitution::associate");
  
  TermList commonTerm;

  TermList* ss=&t1.term;
  TermList* tt=&t2.term;
  TermList* ct=&commonTerm;

  bool mismatch=false;
  
  Stack<TermList*> subterms(64);
  for (;;) {
    if (!ss->sameContent(tt) && TermList::sameTop(ss,tt)) {
      // ss and tt have the same tops and are different, so must be non-variables
      ASS(! ss->isVar());
      ASS(! tt->isVar());

      Term* s = ss->term();
      Term* t = tt->term();
      ct->setTerm(Term::createNonShared(t));

      ASS(s->arity() > 0);
      ASS(s->functor() == t->functor());

      ss = s->args();
      tt = t->args();
      ct = ct->term()->args();
      if (! ss->next()->isEmpty()) {
        subterms.push(ss->next());
        subterms.push(tt->next());
        subterms.push(ct->next());
      }
    } else {
      if (! TermList::sameTop(ss,tt)) {
        if(ss->isVar()) {
          VarSpec sVar=getVarSpec(*ss,t1.index);
          VarSpec ctVar=getAuxVar(sVar);
          ct->makeVar(ctVar.var);
          if(tt->isTerm()) {
            add(ctVar, TermSpec(*tt, t2.index));
          } else {
            makeEqual(sVar,getVarSpec(*tt,t2.index));
          }
        } else if(tt->isVar()) {
          ASS(ss->isTerm())
          VarSpec tVar=getVarSpec(*tt,t2.index);
          VarSpec ctVar=getAuxVar(tVar);
          ct->makeVar(ctVar.index);
          add(tVar, TermSpec(*ss, t1.index));
        } else {
          //tops are different and neither of them is variable, so we can't unify them
          mismatch=true;
          break;
        }
      } else { //ss->sameContent(tt)
	*ct=*ss;
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
        subterms.push(ct->next());
      }
    }
  }
  
  
  
  if(mismatch) {
    if(commonTerm.isTerm()) {
      commonTerm.term()->destroyNonShared();
    }
    commonTerm.makeEmpty();
  } else {
    Term* commonShared=env.sharing->insertRecurrently(commonTerm.term());
    commonTerm.setTerm(commonShared);
  }
  return TermSpec(commonTerm, AUX_INDEX);
}

TermList MMSubstitution::apply(TermList trm, int index)
{
  CALL("MMSubstitution::apply");

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

bool MMSubstitution::occurCheckFails()
{
  CALL("MMSubstitution::occurCheckFails");
  
  Stack<VarSpec> maybeUnref(8);
  Stack<VarSpec> unref(8);
  DHMultiset<VarSpec,VarSpec::Hash1,VarSpec::Hash2> refCounter;
  
  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec vs=bit.nextKey();
    TermSpec ts=_bank.get(vs);
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
string MMSubstitution::toString()
{
  CALL("MMSubstitution::toString");
  string res;
  BankType::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec v(bit.nextKey());
    TermList tl;
    if(v.index==SPECIAL_INDEX) {
      res+="S"+Int::toString(v.var)+" -> ";
      tl.makeSpecialVar(v.var);
    } else {
      res+="X"+Int::toString(v.var)+"/"+Int::toString(v.index)+ " -> ";
      tl.makeVar(v.var);
    }
    tl=apply(tl, v.index);
    res+=Test::Output::singleTermListToString(tl)+"\n";
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
