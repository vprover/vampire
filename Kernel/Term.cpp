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
#include "Term.hpp"

#include "../Indexing/TermSharing.hpp"

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
bool TermList::sameTop(const TermList* ss,const TermList* tt)
{
  if (ss->isVar()) {
    return ss->sameContent(tt);
  }
  if (tt->isVar()) {
    return false;
  }
  return ss->term()->functor() == tt->term()->functor();
}

/**
 * Return true if @b ss and @b tt are both complex terms with the
 * same function symbol.
 */
bool TermList::sameTopFunctor(const TermList* ss,const TermList* tt)
{
  if (ss->isVar() || tt->isVar()) {
    return false;
  }
  return ss->term()->functor() == tt->term()->functor();
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

// /**
//  * Convert the variable to an XML element.
//  */
// XMLElement Term::variableToXML (unsigned var)
// {
//   CALL("Term::variableToXML");

//   XMLElement v("variable",true);
//   v.addAttribute("number",var);
//   return v;
// } // Term::variableToXML

// /**
//  * Convert the term to an XML element.
//  * @since 29/11/2003 Manchester
//  */
// XMLElement Term::toXML() const
// {
//   CALL("Term::toXML");

//   if (isVar()) {
//     return variableToXML(var());
//   }
//   if (isRef()) {
//     return deref()->toXML();
//   }

//   const string& fun = functionName();
//   if (args()->isEmpty()) {
//     XMLElement t("constant",true);
//     t.addAttribute("name",fun);
//     return t;
//   }

//   // non-constant term
//   XMLElement t("term");
//   t.addAttribute("functor",fun);
//   for (const Term* ts = args(); ts->isNonEmpty(); ts = ts->next()) {
//     t.addChild(ts->toXML());
//   }
//   return t;
// } // Term::toXML()


// /**
//  * Convert the literal to an XML element.
//  * @since 29/11/2003 Manchester
//  */
// XMLElement Literal::toXML() const
// {
//   CALL("Literal::toXML");

//   const string& pred = predicateName();
//   if (args()->isEmpty()) {
//     XMLElement t("literal",true);
//     t.addAttribute("predicate",pred);
//     t.addAttribute("sign",isPositive() ? "+" : "-");
//     return t;
//   }

//   // non-constant term
//   XMLElement t("literal");
//   t.addAttribute("predicate",pred);
//   t.addAttribute("sign",isPositive() ? "+" : "-");
//   for (const Term* ts = args(); ts->isNonEmpty(); ts = ts->next()) {
//     t.addChild(ts->toXML());
//   }
//   return t;
// } // Term::toXML()


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
 * Return the result of equality comparison of two arguments
 * to terms.
 * @since 10/06/2007 Manchester
 */
// bool Term::equalArg (const Term* t) const
// {
//   CALL("Term::equalArg");
//   if (isVar()) {
//     return t->isVar() && var() == t->var();
//   }
//   if (t->isVar()) {
//     return false;
//   }
//   return deref()->equals(t->deref());
// } // Term::equalArg

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
  return Hash::hashFNV(reinterpret_cast<const unsigned char*>(_args+1),
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
  return Hash::hashFNV(reinterpret_cast<const unsigned char*>(_args+1),
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
