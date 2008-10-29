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

#include "Term.hpp"
#include "DoubleSubstitution.hpp"

using namespace Kernel;

/**
 * Redefined to do nothing so that on the expansion of double substitutions
 * binding arrays would not get deleted.
 * @since 06/01/2008 Torrevieja
 */
DoubleSubstitution::Subst::~Subst()
{
}

/**
 * When a new array is allocated, the timestamps should be set to 0.
 * @since 06/01/2008 Torrevieja
 */
void DoubleSubstitution::Subst::fillInterval(size_t start, size_t end)
{
  CALL("DoubleSubstitution::Subst::fillInterval");

  for (size_t i = start;i < end;i++) {
    _array[i].timestamp = 0;
  }
} // DoubleSubstitution::Subst::fillInterval

/**
 * Redefined to do nothing so that on the expansion of double substitutions
 * binding arrays would not get deleted.
 * @since 06/01/2008 Torrevieja
 */
DoubleSubstitution::SubstBank::~SubstBank()
{
  CALL("DoubleSubstitution::SubstBank::~SubstBank");

  for (int i = _size-1;i >= 0;i --) {
//     delete [] _array[i].content();
  }
} // DoubleSubstitution::SubstBank::~SubstBank

/**
 * Increase the timestamp. If the wraparound occurs, then reset all
 * all variable bank timestamps to 0.
 */
void DoubleSubstitution::reset()
{
  CALL("DoubleSubstitution::reset");

  _nextVar = 0;
  _timestamp += 2;
  if (_timestamp == 0 || _timestamp == UINT_MAX) {
    _bank.reset();
    _timestamp = 2;
  }
} // DoubleSubstitution::reset

void DoubleSubstitution::SubstBank::reset()
{
  CALL("DoubleSubstitution::SubstBank::reset");

  for (int i = _size-1;i >= 0;i --) {
    _array[i].reset();
  }
} // DoubleSubstitution::SubstBank::reset

/**
 * Bind @b v with the index @b vindex to term @b t with the index @b tindex
 * @pre (v,vindex) must previously be unbound
 * @since 04/01/2008 flight Manchester-Murcia
 */
void DoubleSubstitution::bind(unsigned v,int vindex,TermList t,int tindex)
{
  CALL("DoubleSubstitution::bind");
  Binding& binding = get(v,vindex);

  ASS(binding.timestamp < _timestamp);

  binding.timestamp = _timestamp;
  binding.index = tindex;
  binding.termref = t;
} // DoubleSubstitution::bind

/**
 * Remove the binding for @b v from the substitution.
 * @pre (v,vindex) must previously be unbound
 * @since 04/01/2008 flight Manchester-Murcia
 */
void DoubleSubstitution::unbind(unsigned v,int vindex)
{
  CALL("DoubleSubstitution::unbind");

  Binding& binding = get(v,vindex);

  ASS(binding.timestamp == _timestamp);
  binding.timestamp = 0;
} // DoubleSubstitution::unbind

#if VDEBUG
/**
 * Return the string representation of the substitution.
 * @since 04/01/2008 flight Manchester-Murcia
 */
string DoubleSubstitution::toString() const
{
  CALL("DoubleSubstitution::toString");

  string result("[");
  bool first = true;
  for (unsigned i = 0;i < _bank.size(); i++) {
    const Subst& s = _bank[i];
    for (unsigned j = 0;j < s.size();j++) {
      const Binding& b = s[j];
      if (b.timestamp == _timestamp) {
	if (first) {
	  first = false;
	}
	else {
	  result += ',';
	}
	result += (string)"X" + Int::toString(j) + '/' + Int::toString(i) +
         	  "->" + b.termref.toString() + '/' +
	          Int::toString(b.index);
      }
    }
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

  if (index1 >= index2) {
    _bank.ensure(index1);
  }
  else {
    _bank.ensure(index2);
  }

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
  _bank.ensure(index1 >= index2 ? index1 : index2);

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
    Binding& b = get(from.var(),indexFrom);
    if (b.timestamp != _timestamp) { // not bound
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
 * @since 07/01/2007 Torrevieja
 */
void DoubleSubstitution::apply(TermList* arg,int index,TermList& to)
{
  CALL("DoubleSubstitution::apply(TermList...)");

  TermList ts;
  int ind;

  deref(*arg,index,ts,ind);
  if (ts.isVar()) {
    // unbound variable
    to.makeVar(getVar(ts.var(),ind));
    return;
  }

  Term* t = ts.term();
  if (t->ground()) {
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
 * When collecting the term resulting from the application of the
 * substitution, return the variable number in the new term
 * corresponding to (@b var,@b index).
 * @since 31/03/2008 flight Manchester-Budapest
 */
unsigned DoubleSubstitution::getVar(unsigned var,int index)
{
  CALL("DoubleSubstitution::getVar");

  Binding& bind = get(var,index);
  ASS(bind.timestamp != _timestamp); // unbound
  if (bind.timestamp != _timestamp + 1) {
    bind.timestamp = _timestamp+1;
    bind.termref.makeVar(_nextVar++);
  }
  return bind.termref.var();
} // DoubleSubstitution::getVar
