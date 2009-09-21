/**
 * @file Term.cpp
 * Implements class Term.
 *
 * @since 18/04/2006 Bellevue
 * @since 06/05/2007 Manchester, changed into a single class instead of three
 */

#include <ostream>

#include "../Debug/Tracer.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Set.hpp"
#include "../Lib/Int.hpp"

#include "Signature.hpp"
#include "Substitution.hpp"
#include "Ordering.hpp"

#include "Term.hpp"

#include "../Indexing/TermSharing.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

/**
 * Allocate enough bytes to fit a term of a given arity.
 * @since 01/05/2006 Bellevue
 */
void* Term::operator new(size_t sz,unsigned arity)
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
  try {
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
  } catch(MemoryLimitExceededException) {
    //The MemoryLimitExceededException here can lead to memory leaks,
    //as we miss some subterms.
    stack.reset();
    while(!deletingStack.isEmpty()) {
      deletingStack.pop()->destroy();
    }
    if(!Exception::isThrownDuringExceptionHandling()) {
      throw;
    }
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

  if(!isTerm()) {
    return trm==*this;
  }
  return term()->containsSubterm(trm);
}

bool Term::containsSubterm(TermList trm)
{
  CALL("Term::containsSubterm");
  ASS(!trm.isTerm() || trm.term()->shared());
  ASS(shared());

  if(trm.isTerm() && trm.term()==this) {
    ASS(!isLiteral());
    return true;
  }
  if(arity()==0) {
    return false;
  }

  TermList* ts=args();
  static Stack<TermList*> stack(4);
  stack.reset();
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

bool TermList::containsAllVariablesOf(TermList t)
{
  CALL("Term::containsAllVariablesOf");
  Set<TermList> vars;
  TermIterator oldVars=Term::getVariableIterator(*this);
  while(oldVars.hasNext()) {
    vars.insert(oldVars.next());
  }
  TermIterator newVars=Term::getVariableIterator(t);
  while(newVars.hasNext()) {
    if(!vars.contains(newVars.next())) {
      return false;
    }
  }
  return true;
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
 * Return the string representation of variable term var.
 * @since 16/05/2007
 */
string Term::variableToString (TermList var)
{
  CALL("Term::variableToString");
  ASS(var.isVar());

  if(var.isOrdinaryVar()) {
    return (string)"X" + Int::toString(var.var());
  } else {
    return (string)"S" + Int::toString(var.var());
  }
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
      s += Term::variableToString(*ts);
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

  if(isEmpty()) {
    return "<empty TermList>";
  }
  if (isVar()) {
    return Term::variableToString(*this);
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

#if VDEBUG
  static string nonexisting("<predicate does not exists>");
  if(_functor>=static_cast<unsigned>(env.signature->functions())) {
    return nonexisting;
  }
#endif

  return env.signature->functionName(_functor);
} // Term::functionName

/**
 * Return the print name of the function symbol of this literal.
 * @since 18/05/2007 Manchester
 */
const string& Literal::predicateName() const
{
  CALL("Literal::predicateName");

#if VDEBUG
  static string nonexisting("<predicate does not exists>");
  if(_functor>=static_cast<unsigned>(env.signature->predicates())) {
    return nonexisting;
  }
#endif

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
  CALL("Term::create/2");

  int arity = t->arity();
  Term* s = new(arity) Term(*t);
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    *ss-- = args[i];
  }
  return env.sharing->insert(s);
}

/** Create a new complex term, and insert it into the sharing
 *  structure.
 */
Term* Term::create(unsigned function, unsigned arity, TermList* args)
{
  CALL("Term::create/3");
  ASS_EQ(env.signature->functionArity(function), arity);

  Term* s = new(arity) Term;
  s->makeSymbol(function,arity);

  TermList* ss = s->args();
  for (unsigned i = 0;i < arity;i++) {
    *ss-- = args[i];
  }
  return env.sharing->insert(s);
}

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

void Term::NonVariableIterator::pushNextNonVar(const TermList* t)
{
  while(t->isVar()) {
    t=t->next();
  }
  if(!t->isEmpty()) {
    ASS(t->isTerm());
    _stack.push(t);
  }
}


/**
 * True if there exists another disagreement between the two
 * terms specified in the constructor.
 */
bool Term::DisagreementSetIterator::hasNext()
{
  CALL("Term::DisagreementSetIterator::hasNext");
  ASS(_stack.size()%2==0);

  if(!_arg1.isEmpty()) {
    return true;
  }
  if(_stack.isEmpty()) {
    return false;
  }
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!_stack.isEmpty()) {
    tt=_stack.pop();
    ss=_stack.pop();
    if(!ss->next()->isEmpty()) {
      _stack.push(ss->next());
      _stack.push(tt->next());
    }
    if(!_disjunctVariables && ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      if(ss->term()->arity()) {
	_stack.push(ss->term()->args());
	_stack.push(tt->term()->args());
      }
    } else {
      _arg1=*ss;
      _arg2=*tt;
      return true;
    }
  }
  return false;
}

Comparison Term::lexicographicCompare(TermList t1, TermList t2)
{
  DisagreementSetIterator dsit(t1,t2, false);
  if(dsit.hasNext()) {
	pair<TermList,TermList> dp=dsit.next(); //disagreement pair
	if(dp.first.isTerm()) {
	  if(dp.second.isTerm()) {
	    ASS_NEQ(dp.first.term()->functor(), dp.second.term()->functor());
	    return Int::compare(dp.first.term()->functor(), dp.second.term()->functor());
	  }
	  return Lib::GREATER;
	} else {
	  if(dp.second.isTerm()) {
	    return Lib::LESS;
	  }
	  ASS(dp.first.isOrdinaryVar());
	  ASS(dp.second.isOrdinaryVar());
	  return Int::compare(dp.first.var(), dp.second.var());
	}
  } else {
	return Lib::EQUAL;
  }
}
Comparison Term::lexicographicCompare(Term* t1, Term* t2)
{
  if(t1->isLiteral()) {
	ASS(t2->isLiteral());
	if(static_cast<Literal*>(t1)->header()!=static_cast<Literal*>(t2)->header()) {
	  return (static_cast<Literal*>(t1)->header() > static_cast<Literal*>(t2)->header()) ?
		  Lib::GREATER : Lib::LESS;
	}
  }
  return lexicographicCompare(TermList(t1), TermList(t2));
  if(t1->functor()!=t2->functor()) {
	return (t1->functor() > t2->functor()) ?
		Lib::GREATER : Lib::LESS;
  }
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

unsigned Term::computeDistinctVars() const
{
  Set<unsigned> vars;
  Term::VariableIterator vit(this);
  while(vit.hasNext()) {
    vars.insert(vit.next().var());
  }
  return vars.numberOfElements();
}

/** Create a new literal, and insert it into the sharing
 *  structure.
 */
Literal* Literal::create(unsigned predicate, unsigned arity, bool polarity, bool commutative, TermList* args)
{
  CALL("Literal::create/4");
  ASS_G(predicate, 0); //equality is to be created by createEquality
  ASS_EQ(env.signature->predicateArity(predicate), arity);


  Literal* l = new(arity) Literal(predicate, arity, polarity, commutative);

  TermList* ss = l->args();
  for (unsigned i = 0;i < arity;i++) {
    *ss-- = args[i];
  }
  return env.sharing->insert(l);
}

/** Create a new literal, copy from @b l its predicate symbol and
 *  its arguments, and set its polarity to @b polarity. Insert it
 *  into the sharing structure.
 * @since 07/01/2008 Torrevieja
 */
Literal* Literal::create(Literal* l,bool polarity)
{
  CALL("Literal::create(Literal*,bool)");

  int arity = l->arity();
  Literal* m = new(arity) Literal(*l);
  m->setPolarity(polarity);

  TermList* ts = m->args();
  TermList* ss = l->args();
  while(ss->isNonEmpty()) {
    *ts-- = *ss--;
  }

  return env.sharing->insert(m);
} // Literal::create

/** Create a new literal, copy from @b l its predicate symbol and
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure.
 * @since 07/01/2008 Torrevieja
 */
Literal* Literal::create(Literal* l,TermList* args)
{
  CALL("Literal::create(Literal*,TermList*)");

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
Term::Term(const Term& t) throw()
  : _functor(t._functor),
    _arity(t._arity),
    _weight(0),
    _vars(0)
{
  CALL("Term::Term/1");

  _args[0] = t._args[0];
  _args[0]._info.shared = 0u;
  _args[0]._info.order = 0u;
  _args[0]._info.distinctVars = TERM_DIST_VAR_UNKNOWN;
#if USE_MATCH_TAG
  matchTag().makeEmpty();
#endif
} // Term::Term

/** create a new literal and copy from l its content */
Literal::Literal(const Literal& l) throw()
  : Term(l)
{
  CALL("Literal::Literal/1");
}

/** dummy term constructor */
Term::Term() throw()
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
  _args[0]._info.tag = FUN;
  _args[0]._info.distinctVars = TERM_DIST_VAR_UNKNOWN;
#if USE_MATCH_TAG
  matchTag().makeEmpty();
#endif
} // Term::Term

Literal::Literal()
{
  CALL("Literal::Literal/0");
}

#include <iostream>

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

#endif

std::ostream& Kernel::operator<< (ostream& out, TermList tl )
{
  if(tl.isEmpty()) {
    return out<<"<empty TermList>";
  } else if(tl.isVar()) {
    return out<<Term::variableToString(tl.var());
  } else {
    return out<<tl.term()->toString();
  }
}
std::ostream& Kernel::operator<< (ostream& out, const Term& t )
{
  return out<<t.toString();
}
std::ostream& Kernel::operator<< (ostream& out, const Literal& l )
{
  return out<<l.toString();
}


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
