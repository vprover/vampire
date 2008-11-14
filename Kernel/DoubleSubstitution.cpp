/**
 * @file DoubleSubstitution.cpp
 * Implements class DoubleSubstitution.
 * @since 04/01/2008 flight Manchester-Murcia
 * @since 06/01/2008 Torrevieja, rewritten using arrays and made reusable
 */

#include <climits>

#if VDEBUG
#  include "../Lib/Int.hpp"
#endif

#include "../Lib/DArray.hpp"

#include "Term.hpp"
#include "DoubleSubstitution.hpp"

using namespace Kernel;

/**
 * Increase the timestamp. If the wraparound occurs, then reset all
 * all variable bank timestamps to 0.
 */
void DoubleSubstitution::reset()
{
  CALL("DoubleSubstitution::reset");

  _bank.reset();
} // DoubleSubstitution::reset

/**
 * Bind @b v with the index @b vindex to term @b t with the index @b tindex
 * @pre (v,vindex) must previously be unbound
 * @since 04/01/2008 flight Manchester-Murcia
 */
void DoubleSubstitution::bind(unsigned v,int vindex,TermList t,int tindex)
{
  CALL("DoubleSubstitution::bind/4");
  ASS( vindex!=UNBOUND_INDEX);

  VarSpec vs(v,vindex);
  Binding binding;

  //check that the variable is unbound
  ASS( !_bank.find(vs,binding) || binding.index==UNBOUND_INDEX);

  binding.index = tindex;
  binding.termref = t;

  _bank.set(vs, binding);

} // DoubleSubstitution::bind

/**
 * Remove the binding for @b v from the substitution.
 * @pre (v,vindex) must previously be unbound
 * @since 04/01/2008 flight Manchester-Murcia
 */
void DoubleSubstitution::unbind(unsigned v,int vindex)
{
  CALL("DoubleSubstitution::unbind");

  bool found=_bank.remove(VarSpec(v, vindex));
  
  ASS(found);
} // DoubleSubstitution::unbind

/** 
 * If variable @b var at index @b vindex is bound, return true and
 * assign the binging to result. Otherwise assign unique number 
 * of the variable together with UNBOUND_INDEX to result and return false. 
 */
bool DoubleSubstitution::getBinding(unsigned var,int vindex, Binding& result)
{
  CALL("DoubleSubstitution::getBinding");
  bool found=_bank.find(VarSpec(var,vindex), result);
  if(!found) {
    result.index=UNBOUND_INDEX;
    result.termref.makeVar(_nextVar++);
    _bank.insert(VarSpec(var, vindex), result);
  }
  return result.index!=UNBOUND_INDEX;
}


#if VDEBUG
/**
 * Return the string representation of the substitution.
 * @since 04/01/2008 flight Manchester-Murcia
 */
string DoubleSubstitution::toString() const
{
  CALL("DoubleSubstitution::toString");

  //TODO: Test this method

  string result("[");
  bool first = true;
  BankStorage::Iterator bit(_bank);
  while(bit.hasNext()) {
    VarSpec spec=bit.nextKey();
    Binding binding;
    bool found=_bank.find(spec, binding);
    ASS(found);
    
    if (first) {
      first = false;
    }
    else {
      result += ',';
    }
    result += (string)"X" + Int::toString(spec.var) + '/' + Int::toString(spec.index) +
    	"->" + binding.termref.toString() + '/' +
    	Int::toString(binding.index);
    
  }

  result += ']';
  return result;
} // DoubleSubstitution::toString()
#endif

/**
 * Unify lit1/index1 with lit2/index2 and return the result.
 * @since 05/01/2008 Torrevieja
 */
bool DoubleSubstitution::unify(Literal* lit1,int index1,
			       Literal* lit2,int index2)
{
  CALL("DoubleSubstitution::unify");
  ASS(index1 >= 0);
  ASS(index2 >= 0);

  if (lit1->functor() != lit2->functor() ||
      lit1->polarity() != lit2->polarity()) {
    return false;
  }

  TermList* ts1 = lit1->args();
  if (ts1->isEmpty()) {
    return true;
  }

  if (unify(ts1,index1,lit2->args(),index2)) {
    return true;
  }
  return false;
} // DoubleSubstitution::unify

/**
 * Unify ts1/index1 with ts2/index2 and return the result.
 * @since 05/01/2008 Torrevieja
 */
bool DoubleSubstitution::unifyTerms(TermList* ts1,int index1,
	TermList* ts2,int index2)
{
  TermList aux[4];
  aux[0].makeEmpty();
  aux[1]=*ts1;
  aux[2].makeEmpty();
  aux[3]=*ts2;
  return unify(&aux[1],index1,&aux[3],index2);
}


/**
 * Unify lit1/index1 with lit2/index2 and return the result.
 * @since 05/01/2008 Torrevieja
 */
bool DoubleSubstitution::complementary(Literal* lit1,int index1,
				       Literal* lit2,int index2)
{
  CALL("DoubleSubstitution::complementary");
  ASS(index1 >= 0);
  ASS(index2 >= 0);

  if (lit1->functor() != lit2->functor() ||
      lit1->polarity() == lit2->polarity()) {
    return false;
  }
  if (lit1->arity() == 0) {
    return true;
  }

  if (unify(lit1->args(),index1,lit2->args(),index2)) {
    return true;
  }

  return false;
} // DoubleSubstitution::complementary

/**
 * Dereference (@b from,@b indexFrom) in the following sense:
 * find to what term list and index (@b from,@b indexFrom) is
 * bound and copy this term to @b to and this index to @b indexTo
 * @since 30/03/2008 flight Murcia-Manchester
 */
void DoubleSubstitution::deref(TermList from,int indexFrom,
			       TermList& to,int& indexTo)
{
  CALL("DoubleSubstitution::deref");

  while (from.isVar()) {
    Binding b;
    bool found = getBinding(from.var(),indexFrom, b);
    if (!found) { // not bound
      break;
    }
    indexFrom = b.index;
    from = b.termref;
  }
  to = from;
  indexTo = indexFrom;
} // DoubleSubstitution::deref

/**
 * Unify non-empty lists ts1/index1 and ts2/index2 and return the result.
 * @since 05/01/2008 Torrevieja
 */
bool DoubleSubstitution::unify(TermList* ts1,int index1,
			       TermList* ts2,int index2)
{
  CALL("DoubleSubstitution::unify(TermList...)");

  ASS(! ts1->isEmpty());
  ASS(! ts2->isEmpty());

  static Stack<TermList*> terms(32);
  static Stack<int> indexes(32);
  terms.reset();
  indexes.reset();

  for (;;) {
    // dereference ts1 and ts2
    TermList ss1;
    int i1;
    deref(*ts1,index1,ss1,i1);
    TermList ss2;
    int i2;
    deref(*ts2,index2,ss2,i2);

    if (ss1.isVar()) {
      if (ss2.isVar()) {
	// ss2 is a non-bound variable and b2 a binding for it
	if (i1 != i2 || ss1.var() != ss2.var()) {
	  bind(ss1.var(),i1,ss2,i2);
	}
      }
      else { // ss2 is non-var
	Term* s2 = ss2.term();
	if (! s2->ground() && 
	    occurs(ss1.var(),i1,s2->args(),i2)) {
	  return false;
	}
	bind(ss1.var(),i1,ss2,i2);
      }
    }
    else if (ss2.isVar()) { // ss1 is non-variable
      Term* s1 = ss1.term();
      if (! s1->ground() &&
	  occurs(ss2.var(),i2,s1->args(),i1)) {
	return false;
      }
      bind(ss2.var(),i2,ss1,i1);
    }
    else { // both non-variables
      Term* s1 = ss1.term();
      Term* s2 = ss2.term();
      if (s1->functor() != s2->functor()) {
	return false;
      }
      if (s1->arity() != 0) {
	terms.push(s1->args());
	terms.push(s2->args());
	indexes.push(i1);
	indexes.push(i2);
      }
    }
    ts1 = ts1->next();
    if (! ts1->isEmpty()) {
      ASS(! ts2->isEmpty());
      ts2 = ts2->next();
      continue;
    }
    if (terms.isEmpty()) {
      return true;
    }
    ts1 = terms.pop();
    ts2 = terms.pop();
    index1 = indexes.pop();
    index2 = indexes.pop();
  }
} // DoubleSubstitution::unify


/**
 * True if v1/index1 occurs in t2/index2
 * @since 06/01/2007
 */
bool DoubleSubstitution::occurs(unsigned v,int index,
				TermList* ts2,int index2)
{
  CALL("DoubleSubstitution::occurs");
  ASS(! ts2->isEmpty());

  static Stack<TermList*> terms(16);
  static Stack<int> indexes(16);
  terms.reset();
  indexes.reset();
  for (;;) {
    TermList ss;
    int i;
    deref(*ts2,index2,ss,i);
    if (ss.isVar()) {
      if (i == index && ss.var() == v) {
	return true;
      }
    }
    else { // ss is not a variable
      Term* t = ss.term();
      if (! t->ground()) {
	terms.push(t->args());
	indexes.push(i);
      }
    }
    ts2 = ts2->next();
    if (! ts2->isEmpty()) {
      continue;
    }
    if (terms.isEmpty()) {
      return false;
    }
    ts2 = terms.pop();
    index2 = indexes.pop();
  }
} // DoubleSubstitution::occurs


/**
 * Apply the substitution to @b lit/@b index and return the result
 * (a shared literal)
 * @since 07/01/2007 Torrevieja
 */
Literal* DoubleSubstitution::apply(Literal* lit,int index)
{
  CALL("DoubleSubstitution::apply(Literal...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    apply(args,index,ts[i++]);
  }
  return Literal::create(lit,ts.array());
} // DoubleSubstitution::apply


/**
 * Apply the substitution to the argument of a term @b arg/@ index and save
 * the result (shared term) in the term argument @b to.
 */
void DoubleSubstitution::apply(TermList* arg,int index,TermList& to)
{
  CALL("DoubleSubstitution::apply(TermList...)");

  TermList ts;
  int ind;

  deref(*arg,index,ts,ind);
  if (ts.isVar()) {
    Binding unboundBinding;
    bool res=getBinding(ts.var(), ind, unboundBinding);
    ASS(!res && unboundBinding.index==UNBOUND_INDEX);
    to=unboundBinding.termref;
    return;
  }

  Term* t = ts.term();
  if (t->shared() && t->ground()) {
    to.setTerm(t);
    return;
  }

  unsigned arity = t->arity();
  DArray<TermList> tt(arity);
  int i = 0;
  for (TermList* args = t->args(); ! args->isEmpty(); args = args->next()) {
    apply(args,ind,tt[i++]);
  }
  to.setTerm(Term::create(t,tt.array()));
} // DoubleSubstitution::apply


/**
 * Bind @b v with the index @b vindex to term @b t with the index @b tindex
 * @pre (v,vindex) must previously be unbound
 * @since 04/01/2008 flight Manchester-Murcia
 */
void DoubleSubstitution::backtrackableBind(unsigned v,int vindex,
	TermList t,int tindex,BacktrackData& bd)
{
  CALL("DoubleSubstitution::backtrackableBind");
  
  bind(v,vindex,t,tindex);
  
  bd.addBacktrackObject(new BindBacktrackObject(this,v,vindex));

} // DoubleSubstitution::bind

/**
 * Unify ts1/index1 with ts2/index2 and return the result.
 * @since 05/01/2008 Torrevieja
 */
bool DoubleSubstitution::backtrackableUnifyTerms(TermList ts1,int index1,
	TermList ts2,int index2,BacktrackData& bd)
{
  TermList aux[4];
  aux[0].makeEmpty();
  aux[1]=ts1;
  aux[2].makeEmpty();
  aux[3]=ts2;
  return backtrackableUnify(&aux[1],index1,&aux[3],index2,bd);
}

/**
 * Unify non-empty lists ts1/index1 and ts2/index2 and return the result.
 */
bool DoubleSubstitution::backtrackableUnify(TermList* ts1,int index1,
	TermList* ts2,int index2,BacktrackData& bd)
{
  CALL("DoubleSubstitution::unify(TermList...)");

  ASS(! ts1->isEmpty());
  ASS(! ts2->isEmpty());

  static Stack<TermList*> terms(32);
  static Stack<int> indexes(32);
  terms.reset();
  indexes.reset();

  for (;;) {
    // dereference ts1 and ts2
    TermList ss1;
    int i1;
    deref(*ts1,index1,ss1,i1);
    TermList ss2;
    int i2;
    deref(*ts2,index2,ss2,i2);

    if (ss1.isVar()) {
      if (ss2.isVar()) {
	// ss2 is a non-bound variable and b2 a binding for it
	if (i1 != i2 || ss1.var() != ss2.var()) {
	  backtrackableBind(ss1.var(),i1,ss2,i2,bd);
	}
      }
      else { // ss2 is non-var
	Term* s2 = ss2.term();
	if (! s2->ground() && 
	    occurs(ss1.var(),i1,s2->args(),i2)) {
	  return false;
	}
	backtrackableBind(ss1.var(),i1,ss2,i2,bd);
      }
    }
    else if (ss2.isVar()) { // ss1 is non-variable
      Term* s1 = ss1.term();
      if (! s1->ground() &&
	  occurs(ss2.var(),i2,s1->args(),i1)) {
	return false;
      }
      backtrackableBind(ss2.var(),i2,ss1,i1,bd);
    }
    else { // both non-variables
      Term* s1 = ss1.term();
      Term* s2 = ss2.term();
      if (s1->functor() != s2->functor()) {
	return false;
      }
      if (s1->arity() != 0) {
	terms.push(s1->args());
	terms.push(s2->args());
	indexes.push(i1);
	indexes.push(i2);
      }
    }
    ts1 = ts1->next();
    if (! ts1->isEmpty()) {
      ASS(! ts2->isEmpty());
      ts2 = ts2->next();
      continue;
    }
    if (terms.isEmpty()) {
      return true;
    }
    ts1 = terms.pop();
    ts2 = terms.pop();
    index1 = indexes.pop();
    index2 = indexes.pop();
  }
} // DoubleSubstitution::unify


/**
 * First hash function for DHMap.
 */
unsigned DoubleSubstitution::VarSpec::Hash1::hash(VarSpec& o, int capacity)
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
unsigned DoubleSubstitution::VarSpec::Hash2::hash(VarSpec& o)
{
  return Lib::Hash::hashFNV(reinterpret_cast<const unsigned char*>(&o), sizeof(VarSpec));
}
