/**
 * @file MMSubstitution.cpp
 * Implements Martelli and Montanari unification.
 */

#include "../Lib/Hash.hpp"
#include "../Lib/Environment.hpp"

#include "Kernel.hpp"

bool MMSubstitution::isUnbound(VarSpec v)
{
  CALL("MMSubstitution::isUnbound");
  do {
    TermSpec bind;
    bool found=_bank.find(v,b);
    if(!found || bind.index==UNBOUND_INDEX) {
      return true;
    } else if(bind.term.isTerm()) {
      return false;
    }
    v=VarSpec(bind.term.var(), bind.index);
  }
}

TermSpec MMSubstitution::deref(VarSpec v)
{
  CALL("MMSubstitution::deref");
  do {
    TermSpec binding;
    bool found=_bank.find(v,b);
    if(!found) {
      TermList unboundRef;
      unboundRef.makeVar(_nextUnboundAvailable++);
      bind(v, unboundRef);
      return TermSpec(unboundRef, UNBOUND_INDEX);
    } else if(binding.index==UNBOUND_INDEX || binding.term.isTerm()) {
      return binding;
    }
    v=VarSpec(binding.term.var(), binding.index);
  }
}

void MMSubstitution::bind(const VarSpec& v, const TermSpec& b)
{
  _bank.set(v,b);
}

void MMSubstitution::bindVar(const VarSpec& var, const VarSpec& to)
{
  TermList tl;
  tl.makeVar(to.var);
  _bank.set(v,TermSpec(tl,to.index));
}

VarSpec MMSubstitution::root(VarSpec v)
{
  CALL("MMSubstitution::root");
  do {
    TermSpec bind;
    bool found=_bank.find(v,b);
    if(!found || bind.index==UNBOUND_INDEX || bind.term.isTerm()) {
      return v;
    }
    v=VarSpec(bind.term.var(), bind.index);
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

void MMSubstitution::makeEqual(VarSpec v1, VarSpec v2)
{
  CALL("MMSubstitution::makeEqual");
  //TODO finish
}

TermSpec MMSubstitution::associate(TermSpec t1, TermSpec t2)
{
  CALL("MMSubstitution::associate");

  TermList commonTerm;

  TermList* ss=&t1.term;
  TermList* tt=&t2.term;
  TermList* ct=&commonTerm;

  bool mismatch=false;
  
  Stack<TermList*> subterms(64);
  for (;;) {
    if (!ss->sameContent(tt) && sameTop(ss,tt)) {
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
      if (! sameTop(ss,tt)) {
	//TODO: this part needs to be finished
        int x;
        if(ss->isOrdinaryVar()) {
          if(tt->isTerm()) {
            ct->makeVar(getAuxVar(TermSpec(*ss,t1.index)));
            add(VarSpec(ss->var(), t1.index), TermSpec(*tt, t2.index));
          }
        } else {
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
