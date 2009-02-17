/**
 * @file Term.cpp
 * Implements class Term.
 *
 * @since 18/04/2006 Bellevue
 * @since 06/05/2007 Manchester, changed into a single class instead of three
 */

#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Int.hpp"

#include "Signature.hpp"
#include "Substitution.hpp"
#include "Ordering.hpp"

#include "Term.hpp"

#include "../Indexing/TermSharing.hpp"

#if VDEBUG

#include <ostream>
#include "../Test/Output.hpp"

#endif

using namespace std;
using namespace Lib;
using namespace Kernel;

/**
 * Allocate enough bytes to fit a term of a given arity.
 * @since 01/05/2006 Bellevue
 */
void* Term::operator new(size_t,unsigned arity)
{
  CALL("Term::new");

  return (Term*)ALLOC_KNOWN(sizeof(Term)+arity*sizeof(TermList),"Term");
} // Term::operator new


/**
 * Destroy the term.
 * @since 01/05/2006 Bellevue
 * @since 07/06/2007 Manchester, changed to new data structures
 */
void Term::destroy ()
{
  CALL("Term::destroy");
  ASS(CHECK_LEAKS || ! shared());

  DEALLOC_KNOWN(this,sizeof(Term)+_arity*sizeof(TermList),"Term");
} // Term::destroy

/**
 * If the term is not shared, destroy it and all its nonshared subterms.
 */
void Term::destroyNonShared()
{
  CALL("Term::destroyNonShared");

  if(shared()) {
    return;
  }
  TermList selfRef;
  selfRef.setTerm(this);
  TermList* ts=&selfRef;
  static Stack<TermList*> stack(4);
  static Stack<Term*> deletingStack(8);
  for(;;) {
    if(ts->tag()==REF && !ts->term()->shared()) {
      stack.push(ts->term()->args());
      deletingStack.push(ts->term());
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
  }
  while(!deletingStack.isEmpty()) {
    deletingStack.pop()->destroy();
  }
}

/**
 * Return true if @b ss and @b tt have the same top symbols, that is,
 * either both are the same variable or both are complex terms with the
 * same function symbol.
 * @since 16/08/2008 flight Sydney-San Francisco
 */
bool TermList::sameTop(TermList ss,TermList tt)
{
  if (ss.isVar()) {
    return ss==tt;
  }
  if (tt.isVar()) {
    return false;
  }
  return ss.term()->functor() == tt.term()->functor();
}

/**
 * Return true if @b ss and @b tt are both complex terms with the
 * same function symbol.
 */
bool TermList::sameTopFunctor(TermList ss, TermList tt)
{
  if (!ss.isTerm() || !tt.isTerm()) {
    return false;
  }
  return ss.term()->functor() == tt.term()->functor();
}

/**
 * Return true if @b ss and @b tt are both complex terms with the
 * same function symbol.
 */
bool TermList::equals(TermList t1, TermList t2)
{
  static Stack<TermList*> stack(8);
  ASS(stack.isEmpty());

  TermList* ss=&t1;
  TermList* tt=&t2;
  for(;;) {
    if(ss->isTerm() && tt->isTerm() && (!ss->term()->shared() || !tt->term()->shared())) {
      Term* s=ss->term();
      Term* t=tt->term();
      if(s->functor()!=t->functor()) {
	stack.reset();
	return false;
      }
      stack.push(s->args());
      stack.push(t->args());
    } else if(ss->content()!=tt->content()) {
      stack.reset();
      return false;
    }

    if(stack.isEmpty()) {
      break;
    }
    tt=stack.pop();
    ss=stack.pop();
    if(!tt->next()->isEmpty()) {
      stack.push(ss->next());
      stack.push(tt->next());
    }
  }
  return true;
}

bool TermList::containsSubterm(TermList trm)
{
  CALL("Term::containsSubterm");
  ASS(!trm.isTerm() || trm.term()->shared());

  if(trm==*this) {
    return true;
  }
  if(!isTerm() || term()->arity()==0) {
    return false;
  }
  ASS(term()->shared());
  ASSERT_VALID(*term());

  TermList* ts=term()->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(*ts==trm) {
      return true;
    }
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      ASSERT_VALID(*ts->term());
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    }
    if(stack.isEmpty()) {
      return false;
    }
    ts=stack.pop();
  }
}

/**
 * Return the string representation of variable var.
 * @since 16/05/2007
 */
string Term::variableToString (unsigned var)
{
  CALL("Term::variableToString");

  return (string)"X" + Int::toString(var);
} // variableToString

/**
 * Return the result of conversion of a term into a string.
 * @since 16/05/2007 Manchester
 */
string Term::toString () const
{
  CALL("Term::toString");

  Stack<const TermList*> stack(64);

  string s = functionName();
  if (_arity) {
    s += '(';
    stack.push(args());
    TermList::argsToString(stack,s);
  }
  return s;
} // Term::toString

/**
 * Write to a string term arguments (used in printing literals
 * and terms.
 * @since 16/05/2007 Manchester
 */
void TermList::argsToString(Stack<const TermList*>& stack,string& s)
{
  CALL("TermList::argsToString");

  while (stack.isNonEmpty()) {
    const TermList* ts = stack.pop();
    if (! ts) { // comma
      s += ',';
      continue;
    }
    if (ts->isEmpty()) {
      s += ')';
      continue;
    }
    const TermList* tail = ts->next();
    stack.push(tail);
    if (! tail->isEmpty()) {
      stack.push(0);
    }
    if (ts->isVar()) {
      s += Term::variableToString(ts->var());
      continue;
    }
    const Term* t = ts->term();
    s += t->functionName();
    if (t->arity()) {
      s += '(';
      stack.push(t->args());
    }
  }
} // Term::argsToString

/**
 * Write as a string the head of the term list.
 * @since 27/02/2008 Manchester
 */
string TermList::toString() const
{
  CALL("TermList::toString");
  ASS(isNonEmpty());

  if (isVar()) {
    return Term::variableToString(var());
  }
  return term()->toString();
} // TermList::toString


/**
 * Return the result of conversion of a literal into a string.
 * @since 16/05/2007 Manchester
 */
string Literal::toString () const
{
  CALL("Literal::toString");

  if (isEquality()) {
    const TermList* lhs = args();
    string s = lhs->toString();
    if (isPositive()) {
      s += " = ";
    }
    else {
      s += " != ";
    }
    return s + lhs->next()->toString();
  }

  Stack<const TermList*> stack(64);
  string s = polarity() ? "" : "~";
  s += predicateName();
  if (_arity) {
    s += '(';
    stack.push(args());
    TermList::argsToString(stack,s);
  }
  return s;
} // Literal::toString


/**
 * Return the print name of the function symbol of this term.
 * @since 18/05/2007 Manchester
 */
const string& Term::functionName() const
{
  CALL("Term::functionName");

  return env.signature->functionName(_functor);
} // Term::functionName

/**
 * Return the print name of the function symbol of this literal.
 * @since 18/05/2007 Manchester
 */
const string& Literal::predicateName() const
{
  CALL("Literal::predicateName");

  return env.signature->predicateName(_functor);
} // Literal::predicateName


/**
 * Apply @b subst to the term and return the result.
 * @since 28/12/2007 Manchester
 */
Term* Term::apply(Substitution& subst)
{
  CALL("Term::apply");

  if (ground()) {
    return this;
  }

  bool changed = false;
  Term* t = new(arity()) Term(*this);

  TermList* ss = args();
  TermList* tt = t->args();
  while (! ss->isEmpty()) {
    if (ss->isVar()) {
      unsigned var = ss->var();
      TermList* v = subst.bound(var);
      if (! v) {
	tt->makeVar(var);
      }
      else {
	changed = true;
	if (v->isVar()) {
	  ASS(v->var() != var);
	  tt->makeVar(v->var());
	}
	else {
	  tt->setTerm(v->term());
	}
      }
    }
    else { // ss is not a variable
      Term* s = ss->term();
      Term* r = s->apply(subst);
      tt->setTerm(r);
      if (s != r) {
	changed = true;
      }
    }
    ss = ss->next();
    tt = tt->next();
  }

  return changed ? env.sharing->insert(t) : this;
} // Term::apply


/**
 * Apply @b subst to the literal and return the result.
 * @since 28/12/2007 Manchester
 */
Literal* Literal::apply(Substitution& subst)
{
  CALL("Literal::apply");

  if (ground()) {
    return this;
  }

  bool changed = false;
  Literal* lit = new(arity()) Literal(*this);
  ASS(! lit->shared());

  TermList* ss = args();
  TermList* tt = lit->args();
  while (! ss->isEmpty()) {
    if (ss->isVar()) {
      unsigned var = ss->var();
      TermList* v = subst.bound(var);
      if (! v) {
	tt->makeVar(var);
      }
      else {
	changed = true;
	if (v->isVar()) {
	  ASS(v->var() != var);
	  tt->makeVar(v->var());
	}
	else {
	  tt->setTerm(v->term());
	}
      }
    }
    else { // ss is not a variable
      Term* s = ss->term();
      Term* r = s->apply(subst);
      tt->setTerm(r);
      if (s != r) {
	changed = true;
      }
    }
    ss = ss->next();
    tt = tt->next();
  }

  ASS(! lit->shared());
  return changed ? env.sharing->insert(lit) : this;
} // Literal::apply


/**
 * Return the hash function of the top-level of a complex term.
 * @pre The term must be non-variable
 * @since 28/12/2007 Manchester
 */
unsigned Term::hash() const
{
  CALL("Term::hash");

  unsigned hash = Hash::hash(_functor);
  if (_arity == 0) {
    return hash;
  }
  return Hash::hash(reinterpret_cast<const unsigned char*>(_args+1),
 		       _arity*sizeof(TermList),hash);
} // Term::hash

/**
 * Return the hash function of the top-level of a literal.
 * @since 30/03/2008 Flight Murcia-Manchester
 */
unsigned Literal::hash() const
{
  CALL("Literal::hash");

  unsigned hash = Hash::hash(isPositive() ? (2*_functor) : (2*_functor+1));
  if (_arity == 0) {
    return hash;
  }
  return Hash::hash(reinterpret_cast<const unsigned char*>(_args+1),
 		       _arity*sizeof(TermList),hash);
} // Term::hash


/** Create a new complex term, copy from @b t its function symbol and
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure.
 * @since 07/01/2008 Torrevieja
 */
Term* Term::create(Term* t,TermList* args)
{
  CALL("Term::create");

  int arity = t->arity();
  Term* s = new(arity) Term(*t);
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    *ss-- = args[i];
  }
  return env.sharing->insert(s);
} // Term::create(const Term* t,Term* args)

/** Create a new complex term, copy from @b t its function symbol and
 *  from the array @b args its arguments. Do not insert it into the sharing
 *  structure.
 * @since 07/01/2008 Torrevieja
 */
Term* Term::createNonShared(Term* t,TermList* args)
{
  CALL("Term::createNonShared/2");
  int arity = t->arity();
  Term* s = new(arity) Term(*t);
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    *ss-- = args[i];
  }
  return s;
} // Term::createNonShared(const Term* t,Term* args)

/** Create a new complex term, copy from @b t its function symbol and arity.
 *  Initialize its arguments by a dummy special variable.
 */
Term* Term::createNonShared(Term* t)
{
  CALL("Term::createNonShared/1");
  int arity = t->arity();
  Term* s = new(arity) Term(*t);
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    (*ss--).makeSpecialVar(0);
  }
  return s;
} // Term::createNonShared(const Term* t)

/** Create clone of complex term @b t. Do not insert it into the sharing
 *  structure.
 */
Term* Term::cloneNonShared(Term* t)
{
  CALL("Term::cloneNonShared");
  int arity = t->arity();
  TermList* args = t->args();
  Term* s = new(arity) Term(*t);
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    *ss-- = args[-i];
  }
  return s;
} // Term::cloneNonShared(const Term* t,Term* args)

/**
 * True if there exists next variable
 */
bool Term::VariableIterator::hasNext()
{
  CALL("Term::VariableIterator::hasNext");
  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used && _stack.top()->isVar()) {
    return true;
  }
  while(!_stack.isEmpty()) {
    const TermList* t=_stack.pop();
    if(_used && t->isVar()) {
      _used=false;
      t=t->next();
    }
    if(t->isEmpty()) {
	continue;
    }
    if(t->isVar()) {
      ASS(!_used);
      _stack.push(t);
      return true;
    }
    _stack.push(t->next());
    ASS(t->isTerm());
    const Term* trm=t->term();
    if(!trm->shared() || !trm->ground()) {
      _stack.push(trm->args());
    }
  }
  return false;
}

/**
 * True if there exists next subterm
 */
bool Term::SubtermIterator::hasNext()
{
  CALL("Term::SubtermIterator::hasNext");

  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used) {
    return true;
  }
  _used=false;
  const TermList* t=_stack.pop();
  pushNext(t->next());
  if(t->isTerm()) {
    pushNext(t->term()->args());
  }
  return !_stack.isEmpty();
}

/**
 * True if there exists next subterm
 */
bool Term::PolishSubtermIterator::hasNext()
{
  CALL("Term::PolishSubtermIterator::hasNext");

  if(_stack.isEmpty()) {
    return false;
  }
  if(!_used) {
    return true;
  }
  _used=false;
  const TermList* t=_stack.pop();
  pushNext(t->next());
  return !_stack.isEmpty();
}

/**
 * True if there exists next non-variable subterm
 */
bool Term::NonVariableIterator::hasNext()
{
  CALL("Term::NonVariableIterator::hasNext");

  if(_stack.isEmpty()) {
    return false;
  }
  ASS(_stack.top()->isTerm());
  if(!_used) {
    return true;
  }
  _used=false;
  const TermList* t=_stack.pop();
  pushNextNonVar(t->next());
  pushNextNonVar(t->term()->args());
  return !_stack.isEmpty();
}

/** Return commutative term/literal argument order. */
Term::ArgumentOrder Term::computeArgumentOrder() const
{
  ASS(shared());
  ASS(commutative());
  ASS_EQ(arity(),2);

  Ordering* ord=Ordering::instance();
  switch(ord->compare(*nthArgument(0), *nthArgument(1)))
  {
  case Ordering::GREATER:
    return GREATER;
  case Ordering::LESS:
    return LESS;
  case Ordering::EQUAL:
    return EQUAL;
  case Ordering::INCOMPARABLE:
    return INCOMPARABLE;
  case Ordering::GREATER_EQ:
  case Ordering::LESS_EQ:
  default:
    NOT_IMPLEMENTED;
  }
}


/** Create a new literal, copy from @b l its predicate symbol and
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure.
 * @since 07/01/2008 Torrevieja
 */
Literal* Literal::create(Literal* l,TermList* args)
{
  CALL("Literal::create");

  int arity = l->arity();
  Literal* m = new(arity) Literal(*l);

  TermList* ts = m->args();
  for (int i = 0;i < arity;i++) {
    *ts-- = args[i];
  }
  return env.sharing->insert(m);
} // Literal::create

/** Return a new equality literal, with polarity @b polarity and
 * arguments @b arg1 and @b arg2. Insert it into the sharing structure. */
Literal* Literal::createEquality (bool polarity, TermList arg1, TermList arg2)
{
   CALL("Literal::equality/3");
   Literal* lit=new(2) Literal(0,2,polarity,true);
   *lit->nthArgument(0)=arg1;
   *lit->nthArgument(1)=arg2;
   return env.sharing->insert(lit);
}


/** create a new term and copy from t the relevant part of t's content */
Term::Term(const Term& t)
  : _functor(t._functor),
    _arity(t._arity),
    _weight(0),
    _vars(0)
{
  CALL("Term::Term/1");

  _args[0] = t._args[0];
  _args[0]._info.shared = 0u;
  _args[0]._info.order = 0u;
} // Term::Term

/** create a new literal and copy from l its content */
Literal::Literal(const Literal& l)
  : Term(l)
{
  CALL("Literal::Literal/1");
}

/** dummy term constructor */
Term::Term()
  :_functor(0),
   _arity(0),
   _weight(0),
   _vars(0)
{
  CALL("Term::Term/0");

  _args[0]._info.polarity = 0;
  _args[0]._info.commutative = 0;
  _args[0]._info.shared = 0;
  _args[0]._info.literal = 0;
  _args[0]._info.order = 0;
  _args[0]._info.reserved = 0;
  _args[0]._info.tag = FUN;
} // Term::Term

#if VDEBUG
string Term::headerToString() const
{
  string s("functor: ");
  s += Int::toString(_functor) + ", arity: " + Int::toString(_arity)
    + ", weight: " + Int::toString(_weight)
    + ", vars: " + Int::toString(_vars)
    + ", polarity: " + Int::toString(_args[0]._info.polarity)
    + ", commutative: " + Int::toString(_args[0]._info.commutative)
    + ", shared: " + Int::toString(_args[0]._info.shared)
    + ", literal: " + Int::toString(_args[0]._info.literal)
    + ", order: " + Int::toString(_args[0]._info.order)
    + ", reserved: " + Int::toString(_args[0]._info.reserved)
    + ", tag: " + Int::toString(_args[0]._info.tag);
  return s;
}

void Term::assertValid() const
{
  ASS_ALLOC_TYPE(this, "Term");
  ASS_EQ(_args[0]._info.tag, FUN);
}

void TermList::assertValid() const
{
  if(this->isTerm()) {
    ASS_ALLOC_TYPE(_term, "Term");
    ASS_EQ(_term->_args[0]._info.tag, FUN);
  }
}

std::ostream& Kernel::operator<< (ostream& out, TermList tl )
{
  if(tl.isEmpty()) {
    return out<<"<empty TermList>";
  } else {
    return out<<Test::Output::singleTermListToString(tl);
  }
}
std::ostream& Kernel::operator<< (ostream& out, const Term& t )
{
  return out<<Test::Output::toString(&t);
}
std::ostream& Kernel::operator<< (ostream& out, const Literal& l )
{
  return out<<Test::Output::toString(&l);
}

#endif

/**
 * If the literal has the form p(R,f(S),T), where f(S) is the
 * n-th argument, then return the literal, then return the
 * literal p%f(R,S,T).
 */
Literal* Literal::flattenOnArgument(const Literal* lit,int n)
{
  ASS(lit->shared());

  const TermList* ts = lit->nthArgument(n);
  ASS(! ts->isVar());
  const Term* t = ts->term();
  unsigned newArity = lit->arity() + t->arity() - 1;
  string newName = lit->predicateName() + '%' + Int::toString(n) +
                   '%' + t->functionName();
  unsigned newPredicate = env.signature->addPredicate(newName,newArity);

  Literal* newLiteral = new(newArity) Literal(newPredicate,newArity,
					      lit->polarity(),false);
  // copy all arguments
  TermList* newArgs = newLiteral->args();
  const TermList* args = lit->args();
  for (int i = 0;i < n;i++) {
    *newArgs = *args;
    newArgs = newArgs->next();
    args = args->next();
  }
  // now copy the arguments of t
  for (const TermList* ss=t->args();! ss->isEmpty();ss = ss->next()) {
    *newArgs = *ss;
    newArgs = newArgs->next();
  }
  args = args->next();
  while (! args->isEmpty()) {
    *newArgs = *args;
    newArgs = newArgs->next();
    args = args->next();
  }
  ASS(newArgs->isEmpty());

  return env.sharing->insert(newLiteral);
} // Literal::flattenOnArgument
