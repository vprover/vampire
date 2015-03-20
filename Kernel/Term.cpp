/**
 * @file Term.cpp
 * Implements class Term.
 *
 * @since 18/04/2006 Bellevue
 * @since 06/05/2007 Manchester, changed into a single class instead of three
 */

#include <ostream>

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"

#include "Indexing/TermSharing.hpp"

#include "Formula.hpp"
#include "Signature.hpp"
#include "SortHelper.hpp"
#include "Substitution.hpp"
#include "SubstHelper.hpp"
#include "TermIterators.hpp"

#include "Term.hpp"

/** If non-zero, term ite functors will be always expanded to
 * the ( p ? x : y ) notation on output */
#define ALWAYS_OUTPUT_TERM_ITE 0


using namespace std;
using namespace Lib;
using namespace Kernel;

#if !COMPILER_MSVC 
const unsigned Term::SF_TERM_ITE;
const unsigned Term::SF_LET_TERM_IN_TERM;
const unsigned Term::SF_LET_FORMULA_IN_TERM;
const unsigned Term::SF_FORMULA;
const unsigned Term::SPECIAL_FUNCTOR_LOWER_BOUND;
#endif

/**
 * Allocate enough bytes to fit a term of a given arity.
 * @since 01/05/2006 Bellevue
 */
void* Term::operator new(size_t,unsigned arity, size_t preData)
{
  CALL("Term::new");
  //preData must be a multiply of pointer size to maintain alignment
  ASS_EQ(preData%sizeof(size_t), 0);

  size_t sz = sizeof(Term)+arity*sizeof(TermList)+preData;
  void* mem = ALLOC_KNOWN(sz,"Term");
  mem = reinterpret_cast<void*>(reinterpret_cast<char*>(mem)+preData);
  return (Term*)mem;
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

  size_t sz = sizeof(Term)+_arity*sizeof(TermList);
  void* mem = this;
  mem = reinterpret_cast<void*>(reinterpret_cast<char*>(mem)+getPreDataSize());
  DEALLOC_KNOWN(mem,sz,"Term");
} // Term::destroy

/**
 * If the term is not shared, destroy it and all its nonshared subterms.
 */
void Term::destroyNonShared()
{
  CALL("Term::destroyNonShared");

  if (shared()) {
    return;
  }
  TermList selfRef;
  selfRef.setTerm(this);
  TermList* ts=&selfRef;
  static Stack<TermList*> stack(4);
  static Stack<Term*> deletingStack(8);

  for(;;) {
    if (ts->tag()==REF && !ts->term()->shared()) {
      stack.push(ts->term()->args());
      deletingStack.push(ts->term());
    }
    if (stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
    if (!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
  }
  while (!deletingStack.isEmpty()) {
    deletingStack.pop()->destroy();
  }
}

/**
 * Return true if the term does not contain any unshared proper term.
 *
 * Not containing an unshared term also means that there are no
 * if-then-else or let...in expressions.
 */
bool TermList::isSafe() const
{
  CALL("TermList::isSafe");

  return isVar() || term()->shared();
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
    if (ss->isTerm() && tt->isTerm() && (!ss->term()->shared() || !tt->term()->shared())) {
      Term* s=ss->term();
      Term* t=tt->term();
      if (s->functor()!=t->functor()) {
	stack.reset();
	return false;
      }
      stack.push(s->args());
      stack.push(t->args());
    }
    else if (ss->content()!=tt->content()) {
      stack.reset();
      return false;
    }

    if (stack.isEmpty()) {
      break;
    }
    tt=stack.pop();
    ss=stack.pop();
    if (!tt->next()->isEmpty()) {
      stack.push(ss->next());
      stack.push(tt->next());
    }
  }
  return true;
}

/**
 * Return true if all proper terms in the @ args list are shared
 */
bool TermList::allShared(TermList* args)
{
  while (args->isNonEmpty()) {
    if (args->isTerm() && !args->term()->shared()) {
      return false;
    }
    args = args->next();
  }
  return true;
}

unsigned TermList::weigth() const
{
  return isVar() ? 1 : term()->weight();
}

bool TermList::containsSubterm(TermList trm)
{
  CALL("Term::containsSubterm");

  if (!isTerm()) {
    return trm==*this;
  }
  return term()->containsSubterm(trm);
}

bool Term::containsSubterm(TermList trm)
{
  CALL("Term::containsSubterm");
  ASS(!trm.isTerm() || trm.term()->shared());
  ASS(shared());

  if (trm.isTerm() && trm.term()==this) {
    ASS(!isLiteral());
    return true;
  }
  if (arity()==0) {
    return false;
  }

  TermList* ts=args();
  static Stack<TermList*> stack(4);
  stack.reset();
  for(;;) {
    if (*ts==trm) {
      return true;
    }
    if (!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if (ts->isTerm()) {
      ASSERT_VALID(*ts->term());
      if (ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    }
    if (stack.isEmpty()) {
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
  while (oldVars.hasNext()) {
    vars.insert(oldVars.next());
  }
  TermIterator newVars=Term::getVariableIterator(t);
  while (newVars.hasNext()) {
    if (!vars.contains(newVars.next())) {
      return false;
    }
  }
  return true;
}

bool Term::containsAllVariablesOf(Term* t)
{
  CALL("Term::containsAllVariablesOf");
  static DHSet<TermList> vars;
  vars.reset();

  static VariableIterator vit;

  //collect own vars
  vit.reset(this);
  while (vit.hasNext()) {
    vars.insert(vit.next());
  }

  //check t's vars are among collected
  vit.reset(t);
  while (vit.hasNext()) {
    if (!vars.contains(vit.next())) {
      return false;
    }
  }
  return true;
}

bool Term::isShallow() const
{
  CALL("Term::isShallow");

  const TermList* t = args();
  while (!t->isEmpty()) {
    if (t->isTerm() && t->term()->arity()>0) {
      return false;
    }
    t = t->next();
  }
  return true;
}

TermIterator Term::getVariableIterator(TermList tl)
{
  CALL("Term::getVariableIterator");

  if (tl.isVar()) {
    return pvi( getSingletonIterator(tl) );
  }
  ASS(tl.isTerm());
  return vi( new VariableIterator(tl.term()) );
}


/**
 * Return the string representation of variable var.
 * @since 16/05/2007
 */
vstring Term::variableToString(unsigned var)
{
  CALL("Term::variableToString");

  return (vstring)"X" + Int::toString(var);
} // variableToString

/**
 * Return the string representation of variable term var.
 * @since 16/05/2007
 */
vstring Term::variableToString(TermList var)
{
  CALL("Term::variableToString");
  ASS(var.isVar());

  if (var.isOrdinaryVar()) {
    return (vstring)"X" + Int::toString(var.var());
  }
  else {
    return (vstring)"S" + Int::toString(var.var());
  }
} // variableToString

/**
 * Convert an if-then-else, let...in or formula term to vstring
 */
vstring Term::specialTermToString() const
{
  CALL("Term::specialTermToString");
  ASS(isSpecial());

  switch(functor()) {
  case SF_FORMULA:
  {
    ASS_EQ(arity(),0);
    vstring s = getSpecialData()->getFormula()->toString();
    return s;
  }
  case SF_LET_FORMULA_IN_TERM:
  {
    ASS_EQ(arity(),1);
    vstring s = "(let " + getSpecialData()->getLhsLiteral()->toString();
    s += " := " + getSpecialData()->getRhsFormula()->toString();
    s += " in " + nthArgument(0)->toString();
    s += " )";
    return s;
  }
  case SF_LET_TERM_IN_TERM:
  {
    ASS_EQ(arity(),1);
    vstring s = "( let " + getSpecialData()->getLhsTerm().toString();
    s += " := " + getSpecialData()->getRhsTerm().toString();
    s += " in " + nthArgument(0)->toString();
    s += " )";
    return s;
  }
  case SF_TERM_ITE:
  {
    ASS_EQ(arity(),2);
    vstring s = "$ite_t(" + getSpecialData()->getCondition()->toString();
    s += "," + nthArgument(0)->toString();
    s += "," + nthArgument(1)->toString();
    s += ")";
    return s;
  }
  }
  ASSERTION_VIOLATION;
}

/**
 * Return the result of conversion of a term into a vstring.
 * @since 16/05/2007 Manchester
 */
vstring Term::toString() const
{
  CALL("Term::toString");

  if (isSpecial()) {
    return specialTermToString();
  }

  Stack<const TermList*> stack(64);

  vstring s = isLiteral() ? static_cast<const Literal *>(this)->predicateName() : functionName();
  if (_arity) {
    s += '(';
    stack.push(args());
    TermList::argsToString(stack,s);
  }
  return s;
} // Term::toString

/**
 * Write to a vstring term arguments (used in printing literals
 * and terms.
 * @since 16/05/2007 Manchester
 */
void TermList::argsToString(Stack<const TermList*>& stack,vstring& s)
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
    if (t->isSpecial()) {
      //cerr << t->specialTermToString()<<endl;
      s+=t->specialTermToString();
      continue;
    }
    s += t->functionName();
    if (t->arity()) {
      //cerr << "function: "<< t->functionName()<<endl;
      s += '(';
      stack.push(t->args());
    }
  }
} // Term::argsToString

/**
 * Write as a vstring the head of the term list.
 * @since 27/02/2008 Manchester
 */
vstring TermList::toString() const
{
  CALL("TermList::toString");

  if (isEmpty()) {
    return "<empty TermList>";
  }
  if (isVar()) {
    return Term::variableToString(*this);
  }
  return term()->toString();
} // TermList::toString


/**
 * Return the result of conversion of a literal into a vstring.
 * @since 16/05/2007 Manchester
 */
vstring Literal::toString() const
{
  CALL("Literal::toString");

  if (isEquality()) {
    const TermList* lhs = args();
    vstring s = lhs->toString();
    if (isPositive()) {
      s += " = ";
    }
    else {
      s += " != ";
    }
    return s + lhs->next()->toString();
  }

  Stack<const TermList*> stack(64);
  vstring s = polarity() ? "" : "~";
  s += predicateName();
  //cerr << "predicate: "<< predicateName()<<endl;
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
const vstring& Term::functionName() const
{
  CALL("Term::functionName");

#if VDEBUG
  static vstring nonexisting("<function does not exists>");
  if (_functor>=static_cast<unsigned>(env.signature->functions())) {
    return nonexisting;
  }
#endif

  return env.signature->functionName(_functor);
} // Term::functionName

/**
 * Return the print name of the function symbol of this literal.
 * @since 18/05/2007 Manchester
 */
const vstring& Literal::predicateName() const
{
  CALL("Literal::predicateName");

#if VDEBUG
  static vstring nonexisting("<predicate does not exists>");
  if (_functor>=static_cast<unsigned>(env.signature->predicates())) {
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

  return SubstHelper::apply(this, subst);
} // Term::apply


/**
 * Apply @b subst to the literal and return the result.
 * @since 28/12/2007 Manchester
 */
Literal* Literal::apply(Substitution& subst)
{
  CALL("Literal::apply");

  return SubstHelper::apply(this, subst);
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
  if (isTwoVarEquality()) {
    hash ^= Hash::hash(twoVarEqSort());
  }
  return Hash::hash(reinterpret_cast<const unsigned char*>(_args+1),
 		       _arity*sizeof(TermList),hash);
} // Term::hash

/**
 * Return the hash function of the top-level of a literal with opposite polarity.
 */
unsigned Literal::oppositeHash() const
{
  CALL("Literal::hash");

  unsigned hash = Hash::hash( (!isPositive()) ? (2*_functor) : (2*_functor+1));
  if (_arity == 0) {
    return hash;
  }
  return Hash::hash(reinterpret_cast<const unsigned char*>(_args+1),
 		       _arity*sizeof(TermList),hash);
} // Term::hash

/**
 * Return literal opposite to @b l.
 */
Literal* Literal::complementaryLiteral(Literal* l)
{
  Literal* res=env.sharing->tryGetOpposite(l);
  if (!res) {
    res=create(l,!l->polarity());
  }
  return res;
}


/** Create a new complex term, copy from @b t its function symbol and
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure if all arguments are shared.
 * @since 07/01/2008 Torrevieja
 */
Term* Term::create(Term* t,TermList* args)
{
  CALL("Term::create/2");
  ASS_EQ(t->getPreDataSize(), 0);

  int arity = t->arity();
  Term* s = new(arity) Term(*t);
  bool share = true;
  TermList* ss = s->args();
  for (int i = 0;i < arity;i++) {
    ASS(!args[i].isEmpty());
    *ss-- = args[i];
    if (!args[i].isSafe()) {
      share = false;
    }
  }
  if (share) {
    s = env.sharing->insert(s);
  }
  return s;
}

/** Create a new complex term, and insert it into the sharing
 *  structure if all arguments are shared.
 */
Term* Term::create(unsigned function, unsigned arity, TermList* args)
{
  CALL("Term::create/3");
  ASS_EQ(env.signature->functionArity(function), arity);

  Term* s = new(arity) Term;
  s->makeSymbol(function,arity);

  bool share = true;
  TermList* ss = s->args();

  TermList* curArg = args;
  TermList* argStopper = args+arity;
  while (curArg!=argStopper) {
    *ss = *curArg;
    --ss;
    if (!curArg->isSafe()) {
      share = false;
    }
    ++curArg;
  }
  if (share) {
    s = env.sharing->insert(s);
  }
  return s;
}

/** Create a new constant and insert in into the sharing
 *  structure.
 */
Term* Term::createConstant(const vstring& name)
{
  CALL("Term::createConstant");

  unsigned symbolNumber = env.signature->addFunction(name,0);
  return createConstant(symbolNumber);
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
    ASS(!args[i].isEmpty());
    *ss-- = args[i];
  }
  return s;
} // Term::createNonShared(const Term* t,Term* args)

/**
 * Create a (condition ? thenBranch : elseBranch) expression
 * and return the resulting term
 */
Term* Term::createTermITE(Formula * condition, TermList thenBranch, TermList elseBranch)
{
  CALL("Term::createTermITE");
  Term* s = new(2,sizeof(SpecialTermData)) Term;
  s->makeSymbol(SF_TERM_ITE, 2);
  TermList* ss = s->args();
  *ss = thenBranch;
  ss = ss->next();
  *ss = elseBranch;
  ASS(ss->next()->isEmpty());
  s->getSpecialData()->_termITEData.condition = condition;
  return s;
}

/**
 * Create (let lhs <- rhs in t) expression and return
 * the resulting term
 */
Term* Term::createTermLet(TermList lhs, TermList rhs, TermList t)
{
  CALL("Term::createTermLet");
  ASS(lhs.isSafe());
  ASS(lhs.isVar() || lhs.term()->hasOnlyDistinctVariableArgs());

  Term* s = new(1,sizeof(SpecialTermData)) Term;
  s->makeSymbol(SF_LET_TERM_IN_TERM, 1);
  TermList* ss = s->args();
  *ss = t;
  ASS(ss->next()->isEmpty());
  s->getSpecialData()->_termLetData.lhs = lhs.content();
  s->getSpecialData()->_termLetData.rhs = rhs.content();
  return s;
}

/**
 * Create (let lhs <- rhs in f) expression and return
 * the resulting term
 */
Term* Term::createFormulaLet(Literal* lhs, Formula* rhs, TermList t)
{
  CALL("Term::createFormulaLet");
  ASS(lhs->shared());
  ASS(lhs->hasOnlyDistinctVariableArgs());

  Term* s = new(1,sizeof(SpecialTermData)) Term;
  s->makeSymbol(SF_LET_FORMULA_IN_TERM, 1);
  TermList* ss = s->args();
  *ss = t;
  ASS(ss->next()->isEmpty());
  s->getSpecialData()->_formulaLetData.lhs = lhs;
  s->getSpecialData()->_formulaLetData.rhs = rhs;
  return s;
}

/**
 * Create a formula expression and return
 * the resulting term
 */
Term* Term::createFormula(Formula* formula)
{
  CALL("Term::createFormula");

  Term* s = new(0,sizeof(SpecialTermData)) Term;
  s->makeSymbol(SF_FORMULA, 0);
  s->getSpecialData()->_formulaData.formula = formula;
  return s;
}

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

Term* Term::create1(unsigned fn, TermList arg)
{
  CALL("Term::create1");

  return Term::create(fn, 1, &arg);
}

Term* Term::create2(unsigned fn, TermList arg1, TermList arg2)
{
  CALL("Term::create2");

  TermList args[] = {arg1, arg2};
  return Term::create(fn, 2, args);
}


unsigned Term::computeDistinctVars() const
{
  Set<unsigned> vars;
  VariableIterator vit(this);
  while (vit.hasNext()) {
    vars.insert(vit.next().var());
  }
  return vars.size();
}

/**
 * Return true if term/literal has only variable subterms and they all are distinct
 */
bool Term::hasOnlyDistinctVariableArgs() const
{
  CALL("Term::hasOnlyDistinctVariableArgs");

  if (getDistinctVars()!=arity()) {
    return false;
  }
  if (weight()!=arity()+1) {
    return false;
  }
  return true;
}

/**
 * True if each function and predicate symbols in this term or literal are
 * marked as skip for the purpose of symbol elimination.
 * @since 04/05/2013 Manchester, changed to use the new NonVariable Iterator
 * @author Andrei Voronkov
 */
bool Term::skip() const
{
  if (isLiteral()) {
    if (!env.signature->getPredicate(functor())->skip()) {
      return false;
    }
  }
  else {
    if (!env.signature->getFunction(functor())->skip()) {
      return false;
    }
  }
  NonVariableIterator nvi(const_cast<Term*>(this));
  while (nvi.hasNext()) {
    unsigned func=nvi.next().term()->functor();
    if (!env.signature->getFunction(func)->skip()) {
      return false;
    }
  }
  return true;
} // skip

/**
 * Return true iff headers of literals match each other. We check also whether
 * sorts of equality literals are equal.
 */
bool Literal::headersMatch(Literal* l1, Literal* l2, bool complementary)
{
  CALL("Literal::headersMatch");
  if (l1->_functor!=l2->_functor || (complementary?1:0)!=(l1->polarity()!=l2->polarity())) {
    return false;
  }
  if (l1->isEquality()) {
    if (SortHelper::getEqualityArgumentSort(l1)!=SortHelper::getEqualityArgumentSort(l2)) {
      return false;
    }
  }
  return true;
}

/** Create a new literal, and insert it into the sharing
 *  structure if all arguments are shared.
 */
Literal* Literal::create(unsigned predicate, unsigned arity, bool polarity, bool commutative, TermList* args)
{
  CALL("Literal::create/4");
  ASS_G(predicate, 0); //equality is to be created by createEquality
  ASS_EQ(env.signature->predicateArity(predicate), arity);


  Literal* l = new(arity) Literal(predicate, arity, polarity, commutative);

  bool share = true;
  TermList* ss = l->args();
  for (unsigned i = 0;i < arity;i++) {
    *ss-- = args[i];
    if (!args[i].isSafe()) {
      share = false;
    }
  }
  if (share) {
    l = env.sharing->insert(l);
  }
  return l;
}

/** Create a new literal, copy from @b l its predicate symbol and
 *  its arguments, and set its polarity to @b polarity. Insert it
 *  into the sharing structure if all arguments are shared.
 * @since 07/01/2008 Torrevieja
 */
Literal* Literal::create(Literal* l,bool polarity)
{
  CALL("Literal::create(Literal*,bool)");
  ASS_EQ(l->getPreDataSize(), 0);

  if (l->isEquality()) {
    return createEquality(polarity, *l->nthArgument(0), *l->nthArgument(1), SortHelper::getEqualityArgumentSort(l));
  }

  int arity = l->arity();
  Literal* m = new(arity) Literal(*l);
  m->setPolarity(polarity);

  TermList* ts = m->args();
  TermList* ss = l->args();
  while (ss->isNonEmpty()) {
    *ts-- = *ss--;
  }
  if (l->shared()) {
    if (l->isTwoVarEquality()) {
      m = env.sharing->insertVariableEquality(m, l->twoVarEqSort());
    }
    else {
      m = env.sharing->insert(m);
    }
  }
  return m;
} // Literal::create

/** Create a new literal, copy from @b l its predicate symbol and
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure if all arguments are shared.
 * @since 07/01/2008 Torrevieja
 */
Literal* Literal::create(Literal* l,TermList* args)
{
  CALL("Literal::create(Literal*,TermList*)");
  ASS_EQ(l->getPreDataSize(), 0);

  if (l->isEquality()) {
    return createEquality(l->polarity(), args[0], args[1], SortHelper::getEqualityArgumentSort(l));
  }

  int arity = l->arity();
  Literal* m = new(arity) Literal(*l);

  bool share = true;
  TermList* ts = m->args();
  for (int i = 0;i < arity;i++) {
    *ts-- = args[i];
    if (!args[i].isSafe()) {
      share = false;
    }
  }
  if (share) {
    m = env.sharing->insert(m);
  }
  return m;
} // Literal::create

/**
 * Return a new equality literal, with polarity @b polarity and
 * arguments @b arg1 and @b arg2. These arguments must be of sort @c sort.
 * Insert the new literal into the sharing structure if all arguments
 * are shared.
 *
 * The equality may be between two variables.
 */
Literal* Literal::createEquality (bool polarity, TermList arg1, TermList arg2, unsigned sort)
{
   CALL("Literal::createEquality/4");

   unsigned srt1, srt2;

   if (!SortHelper::tryGetResultSort(arg1, srt1)) {
     if (!SortHelper::tryGetResultSort(arg2, srt2)) {
       if (arg1.isVar() && arg2.isVar()) {
	 return createVariableEquality(polarity, arg1, arg2, sort);
       }
       return createSpecialTermVariableEquality(polarity, arg1, arg2, sort);
     }
     ASS_EQ(srt2, sort);
   }
   else {
     ASS_EQ(srt1, sort);
#if VDEBUG
     if (SortHelper::tryGetResultSort(arg2, srt2)) {
       ASS_EQ(srt2, sort);
     }
#endif
   }
   Literal* lit=new(2) Literal(0,2,polarity,true);
   *lit->nthArgument(0)=arg1;
   *lit->nthArgument(1)=arg2;
   if (arg1.isSafe() && arg2.isSafe()) {
     lit = env.sharing->insert(lit);
   }
   return lit;
}

/**
 * Create a literal that is equality between two variables.
 */
Literal* Literal::createVariableEquality (bool polarity, TermList arg1, TermList arg2, unsigned variableSort)
{
  CALL("Literal::createVariableEquality");
  ASS(arg1.isVar());
  ASS(arg2.isVar());

  Literal* lit=new(2) Literal(0,2,polarity,true);
  *lit->nthArgument(0)=arg1;
  *lit->nthArgument(1)=arg2;
  lit = env.sharing->insertVariableEquality(lit, variableSort);
  return lit;
}

/**
 * Create a literal that is equality conteining variables and special
 * terms for which their sort cannot be determined.
 */
Literal* Literal::createSpecialTermVariableEquality (bool polarity, TermList arg1, TermList arg2, unsigned sort)
{
  CALL("Literal::createVariableEquality");
  ASS(arg1.isTerm() || arg2.isTerm());
#if VDEBUG
  unsigned aux;
  ASS(!SortHelper::tryGetResultSort(arg1, aux));
  ASS(!SortHelper::tryGetResultSort(arg2, aux));
#endif

  Literal* lit=new(2) Literal(0,2,polarity,true);
  *lit->nthArgument(0)=arg1;
  *lit->nthArgument(1)=arg2;
  lit->markTwoVarEquality();
  lit->setTwoVarEqSort(sort);
  return lit;
}


Literal* Literal::create1(unsigned predicate, bool polarity, TermList arg)
{
  CALL("Literal::create1");

  return Literal::create(predicate, 1, polarity, false, &arg);
}

Literal* Literal::create2(unsigned predicate, bool polarity, TermList arg1, TermList arg2)
{
  CALL("Literal::create2");
  ASS_NEQ(predicate, 0);

  TermList args[] = {arg1, arg2};
  return Literal::create(predicate, 2, polarity, false, args);
}


/** create a new term and copy from t the relevant part of t's content */
Term::Term(const Term& t) throw()
  : _functor(t._functor),
    _arity(t._arity),
    _color(COLOR_TRANSPARENT),
    _hasInterpretedConstants(0),
    _isTwoVarEquality(0),
    _weight(0),
    _vars(0)
{
  CALL("Term::Term/1");
  ASS(!isSpecial()); //we do not copy special terms

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
   _color(COLOR_TRANSPARENT),
   _hasInterpretedConstants(0),
   _isTwoVarEquality(0),
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
vstring Term::headerToString() const
{
  vstring s("functor: ");
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
  if (this->isTerm()) {
    ASS_ALLOC_TYPE(_term, "Term");
    ASS_EQ(_term->_args[0]._info.tag, FUN);
  }
}

#endif

std::ostream& Kernel::operator<< (ostream& out, TermList tl )
{
  if (tl.isEmpty()) {
    return out<<"<empty TermList>";
  }
  if (tl.isVar()) {
    return out<<Term::variableToString(tl);
  }
  return out<<tl.term()->toString();
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
  vstring newName = lit->predicateName() + '%' + Int::toString(n) +
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
