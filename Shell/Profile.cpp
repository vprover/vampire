/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Shell/Profile.cpp (syntactic properties of problems)
 *
 * @since 15/06/2008 Kemerovo
 */

#include "Debug/Tracer.hpp"
#include "Lib/Int.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Profile.hpp"

using namespace Kernel;
using namespace Shell;

void Profile::output(const Term* term,ostream& str)
{
  if (term->arity() == 0) {
    str << 'c' << term->functor();
    return;
  }
  str << 'f' << term->functor();
  output(term->args(),str);
}

void Profile::output(const TermList* ts,ostream& str)
{
  str << '(';
  bool first = true;
  do {
    if (first) {
      first = false;
    }
    else {
      str << ',';
    }
    if (ts->isVar()) {
      str << 'X' << ts->var();
    }
    else {
      output(ts->term(),str);
    }
    ts = ts->next();
  }
  while (! ts->isEmpty());
  str << ')';
}

void Profile::output(const Literal* lit,ostream& str,char pred)
{
  str << pred << lit->functor() << '(';
  for (const TermList* ts = lit->args();! ts->isEmpty();ts = ts->next()) {
    if (ts->isVar()) {
      str << 'X' << ts->var();
    }
    else {
      output(ts->term(),str);
    }
    str << ',';
  }
}

void Profile::output(const Clause* clause,ostream& str)
{
  static int lastPredicate = -1;
  static bool nonUnitFound;

  int length = clause->length();
  const Literal* head = (*clause)[0];
  int headPredicate = head->functor();

  int firstLiteral;
//   if (head->isEquality()) {
//     return;
//   }
  if (head->isNegative()) {
    if (clause->inputType() == Unit::AXIOM) {
      return;
    }
    firstLiteral = 0;
    str << "g(T):-";
    goto nonunit;
  }

  if (headPredicate != lastPredicate) {
    lastPredicate = headPredicate;
    nonUnitFound = false;
  }

  if (length == 1) {
    output(head,str,'p');
    str << "_).\n";
    return;
  }

  // length >= 1
  if (! nonUnitFound) {
    nonUnitFound = true;
    int pred = head->functor();
    int arity = head->arity();
    str << 'p' << pred << '(';
    for (int i = arity-1;i >= 0;i--) {
      str << "_,";
    }
    str << "0):-!,fail.\n";
    str << 'p' << pred << '(';
    for (int i = 0;i < arity;i++) {
      str << 'X' << i << ',';
    }
    str << "T):-T1 is T-1,";
    str << 'q' << pred << '(';
    for (int i = 0;i < arity;i++) {
      str << 'X' << i << ',';
    }
    str << "T1).\n";
  }

  output(head,str,'q');
  str << "T):-";

  if (length == 2) {
    output((*clause)[1],str,'p');
    str << "T).\n";
    return;
  }

  firstLiteral = 1;
 nonunit:
  Sort<const Literal*,Profile> sort(length-firstLiteral,*this);
  for (int i = firstLiteral;i < length;i++) {
    sort.add((*clause)[i]);
  }
  sort.sort();
  for (int i = firstLiteral;i < length;i++) {
    if (i > firstLiteral) {
      str << ',';
    }
    output(sort[i-firstLiteral],str,'p');
    str << "T)";
  }
  str << ".\n";
}

Profile::VarCounter::VarCounter()
  : Array<const Clause*>(15)
{
  CALL("Profile::VarCounter::VarCounter");

  fillInterval(0,15);
} // Profile::VarCounter::VarCounter

void Profile::VarCounter::fillInterval(size_t start,size_t end)
{
  CALL("Profile::VarCounter::fillInterval");

  for (size_t i = start;i < end;i++) {
    _array[i] = 0;
  }
} // Profile::VarCounter::fillInterval

/** 
 * Initialize Profile.
 * @since 15/06/2008 Kemerovo
 */
Profile::Profile ()
  : _numberOfClauses(0)
{
  CALL("Profile::Profile");

  for (int i = HOW_MANY-1;i >= 0;i--) {
    _vars[i] = 0;
  }
  for (int i = HOW_MANY-1;i >= 0;i--) {
    _syms[i] = 0;
  }
  for (int i = HOW_MANY-1;i >= 0;i--) {
    _lits[i] = 0;
  }

  Signature* sig = env.signature;
  int fn = sig->functions();
  _funs = (int*)ALLOC_UNKNOWN(sizeof(int)*fn,"Profile::funs");
  _funClauses = (const Clause**)ALLOC_UNKNOWN(sizeof(Clause*)*fn,
					      "Profile::funClauses");
  int pd = sig->predicates();
  _posPreds = (int*)ALLOC_UNKNOWN(sizeof(int)*pd,"Profile::preds");
  _negPreds = (int*)ALLOC_UNKNOWN(sizeof(int)*pd,"Profile::preds");
  _predClauses = (const Clause**)ALLOC_UNKNOWN(sizeof(Clause*)*pd,
					       "Profile::predClauses");
} // Profile::Profile

Profile::~Profile()
{
  CALL("Profile::~Profile");

  DEALLOC_UNKNOWN(_funs,"Profile::funs");
  DEALLOC_UNKNOWN(_funClauses,"Profile::funClauses");
  DEALLOC_UNKNOWN(_posPreds,"Profile::posPreds");
  DEALLOC_UNKNOWN(_negPreds,"Profile::negPreds");
  DEALLOC_UNKNOWN(_predClauses,"Profile::predClauses");
} // Profile::~Profile


/** 
 * Scan profile from a problem.
 * @since 15/06/2008 Kemerovo
 */
void Profile::scan(const UnitList* units)
{
  CALL("Profile::scan(UnitList*)");

  Signature* sig = env.signature;
  int fn = sig->functions();
  for (int i = fn-1;i >= 0;i--) {
    _funs[i] = 0;
  }
  for (int i = fn-1;i >= 0;i--) {
    _funClauses[i] = 0;
  }
  int pd = sig->predicates();
  for (int i = pd-1;i >= 0;i--) {
    _posPreds[i] = 0;
  }
  for (int i = pd-1;i >= 0;i--) {
    _negPreds[i] = 0;
  }
  for (int i = pd-1;i >= 0;i--) {
    _predClauses[i] = 0;
  }

  UnitList::Iterator us(units);
  int numberOfClauses = 0;
  while (us.hasNext()) {
    numberOfClauses++;
    scan(static_cast<const Clause*>(us.next()));
  }

  for (int p = 0;p < pd;p++) {
    if (_posPreds[p]) {
      continue;
    }
    cout << 'p' << p << '(';
    for (int i = sig->predicateArity(p)-1;i >= 0;i--) {
      cout << "_,";
    }
    cout << "_):-!,fail.\n";
  }

  Sort<Clause*,Profile> sort(numberOfClauses,*this);
  // evaluate clauses and count the number of clauses that can be used at all
  UnitList::Iterator vs(units);
  int useful = 0;
  while (vs.hasNext()) {
    Clause* c = static_cast<Clause*>(vs.next());
    int w = evaluate(c);
    c->setAge(w);

    if (w != -1 || c->inputType() != Unit::AXIOM) {
      useful++;
      sort.add(c);
    }
  }

  sort.sort();
  for (int i = 0;i < useful;i++) {
//     cout << sort[i]->toString() << ' ' << sort[i]->age() << "\n";
    output(sort[i],cout);
  }
  cout << "main:-gg(0).\n"
          "gg(T):-writeln(T),g(T),writeln('yes!'),halt.\n"
          "gg(T):-T1 is T+1,gg(T1).\n";
} // Profile::scan(const UnitList* units)

/**
 * Scan a clause.
 * @since 15/06/2008 Kemerovo
 */
void Profile::scan (const Clause* clause)
{
  CALL("Profile::scan (const Clause*)");

  _varsInThisClause = 0;
  _symsInThisClause = 0;
  _currentClause = clause;

  int length = clause->length();
  for (int i = length-1;i >= 0;i--) {
    const Literal* lit = (*clause)[i];
    scan(lit);
    if (i != 0 && lit->isPositive()) { // the literal is positive and not first
      // make it first
      (*clause)[i] = (*clause)[0];
      (*clause)[0] = lit;
    }
  }

  if (_varsInThisClause < HOW_MANY-1) {
    _vars[_varsInThisClause]++;
  }
  else {
    _vars[HOW_MANY-1]++;
  }
  if (_symsInThisClause < HOW_MANY-1) {
    _syms[_symsInThisClause]++;
  }
  else {
    _syms[HOW_MANY-1]++;
  }
  if (length < HOW_MANY-1) {
    _lits[length]++;
  }
  else {
    _lits[HOW_MANY-1]++;
  }
} // Profile::scan (const Clause* clause, bool isAxiom)


/**
 * Scan a literal.
 * @since 15/06/2008 Kemerovo
 */
void Profile::scan (const Literal* lit)
{
  CALL("Profile::scan (const Literal*...)");
  if (lit->isPositive()) {
    _posPreds[lit->functor()]++;
  }
  else {
    _negPreds[lit->functor()]++;
  }
  if (_predClauses[lit->functor()] != _currentClause) {
    _predClauses[lit->functor()] = _currentClause;
    _symsInThisClause++;
//     if (lit->isEquality()) {
//       cout << _currentClause->toString() << "\n";
//     }
  }
  scan(lit->args());
} // Profile::scan (const Atom& term, bool& isGround)

/**
 * Scan a term arguments.
 * @since 15/06/2008 Kemerovo
 */
void Profile::scan(const TermList* ts)
{
  CALL("Profile::scan(TermList*))");

  Stack<const TermList*> stack(64);

  for (;;) {
    if (ts->isEmpty()) {
      if (stack.isEmpty()) {
	return;
      }
      ts = stack.pop();
    }
    // ts is non-empty
    if (ts->isVar()) {
      int v = ts->var();
      if (vc[v] != _currentClause) {
	vc[v] = _currentClause;
	_varsInThisClause++;
      }
    }
    else { // ts is a reference to a complex term
      const Term* t = ts->term();
      _funs[t->functor()]++;
      if (_funClauses[t->functor()] != _currentClause) {
	_funClauses[t->functor()] = _currentClause;
	_symsInThisClause++;
      }
      const TermList* ss = t->args();
      if (! ss->isEmpty()) {
	stack.push(ss);
      }
    }
    ts = ts->next();
  }
} // Profile::scan (const TermList*)


/**
 * Output the profile to a string readable by a human. NOT ALL FIELDS
 * ARE CURRENTLY OUTPUT.
 * @since 15/06/2008 Kemerovo
 */
vstring Profile::toString () const
{
  vstring result("");

  result += (vstring)"Variables\n";
  for (int i = 0; i < HOW_MANY-1;i++) {
    result += vstring("  ") + Int::toString(i) + ':'
      + Int::toString(_vars[i]) + '\n';
  }
  result += vstring(" >") + Int::toString(HOW_MANY-2) + ':'
    + Int::toString(_vars[HOW_MANY-1]) + '\n';

  result += (vstring)"Symbols\n";
  for (int i = 0; i < HOW_MANY-1;i++) {
    result += vstring("  ") + Int::toString(i) + ':'
      + Int::toString(_syms[i]) + '\n';
  }
  result += vstring(" >") + Int::toString(HOW_MANY-2) + ':'
    + Int::toString(_syms[HOW_MANY-1]) + '\n';

  result += (vstring)"Literals\n";
  for (int i = 0; i < HOW_MANY-1;i++) {
    result += vstring("  ") + Int::toString(i) + ':'
      + Int::toString(_lits[i]) + '\n';
  }
  result += vstring(" >") + Int::toString(HOW_MANY-2) + ':'
    + Int::toString(_lits[HOW_MANY-1]) + '\n';

  Signature* sig = env.signature;

  result += "Functions with more than 10 occurrences:\n";
  int fn = sig->functions();
  for (int i = fn-1;i >= 0;i--) {
    if (_funs[i] > 10) {
      result += vstring("  ") + Int::toString(_funs[i]) + ": " +
	sig->functionName(i) + '\n';
    }
  }
  result += "Predicates with more than 10 occurrences:\n";
  int pd = sig->predicates();
  for (int i = pd-1;i >= 0;i--) {
    int pos = _posPreds[i];
    int neg = _negPreds[i];
    if (pos < 2 || neg < 2 || pos+neg > 10) {
      result += vstring("  ") + Int::toString(pos) + '/' + Int::toString(neg)
	+ ": " + sig->predicateName(i) + '\n';
    }
  }

  return result;
} // Profile::toString

/**
 * Evaluate the clause.
 * @return the following value:
 * <ul>
 * <li>-1 if it has no positive literals and is non-goal (such clauses
 * should be discarded);</li>
 * <li>0 if the clause is unit;</li>
 * <li>product, over all negative literals in it, of the number of 
 * positive occurrences of the predicate of this literal.</li>
 * </ul>
 * @since 15/06/2008 Kemerovo
 */
int Profile::evaluate(const Clause* c)
{
  CALL("Profile::evaluate");

  bool hasPos = false;
  int length = c->length();
  int product = 1;
  for (int i = length-1;i >= 0;i--) {
    const Literal* lit = (*c)[i];
    if (lit->isPositive()) {
      hasPos = true;
    }
    else {
      int prod = product * _posPreds[lit->functor()];
      if (prod != 0 && prod < product) { // overflow
	return INT_MAX;
      }
      product = prod;
    }
  }
  if (! hasPos) {
    return -1;
  }
  if (length == 1) {
    return 0;
  }

  if (product == 0) {
    return 1; // this clause should be discarded as well
  }
  return product+1;
} // Profile::evaluate

/**
 * Compare two clauses using their ages.
 * @since 27/06/2008 Manchester
 */
bool Profile::lessThan(const Clause* c1,const Clause* c2)
{
  int pred1 = (*c1)[0]->functor();
  int pred2 = (*c2)[0]->functor();
  if (pred1 < pred2) {
    return true;
  }
  if (pred2 < pred1) {
    return false;
  }
  return c1->age() < c2->age();
} // Profile::lessThan

/**
 * Compare two literals using (1) the number of occurrences of their
 * predicate in the problem; (2) weight.
 * @since 28/06/2008 Manchester
 */
bool Profile::lessThan(const Literal* lit1,const Literal* lit2)
{
  int occ1 = _posPreds[lit1->functor()];
  int occ2 = _posPreds[lit2->functor()];
  if (occ1 < occ2) {
    return true;
  }
  if (occ2 < occ1) {
    return false;
  }
  return lit1->weight() < lit2->weight();
} // Profile::lessThan
