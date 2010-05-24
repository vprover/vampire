/**
 * @file CASC.cpp (syntactic properties of problems)
 *
 * @since 15/06/2008 Kemerovo
 */

#include <climits>

#include "Debug/Tracer.hpp"
#include "Lib/Int.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Rule.hpp"
#include "CASC.hpp"

using namespace Kernel;
using namespace Rule;

// void CASC::output(const Term* term,ostream& str)
// {
//   if (term->arity() == 0) {
//     str << 'c' << term->functor();
//     return;
//   }
//   str << 'f' << term->functor();
//   output(term->args(),str);
// }

// void CASC::output(const TermList* ts,ostream& str)
// {
//   str << '(';
//   bool first = true;
//   do {
//     if (first) {
//       first = false;
//     }
//     else {
//       str << ',';
//     }
//     if (ts->isVar()) {
//       str << 'X' << ts->var();
//     }
//     else {
//       output(ts->term(),str);
//     }
//     ts = ts->next();
//   }
//   while (! ts->isEmpty());
//   str << ')';
// }

// void CASC::output(const Literal* lit,ostream& str,char pred)
// {
//   str << pred << lit->functor() << '(';
//   for (const TermList* ts = lit->args();! ts->isEmpty();ts = ts->next()) {
//     if (ts->isVar()) {
//       str << 'X' << ts->var();
//     }
//     else {
//       output(ts->term(),str);
//     }
//     str << ',';
//   }
// }

// void CASC::output(const Clause* clause,ostream& str)
// {
//   static int lastPredicate = -1;
//   static bool nonUnitFound;

//   int length = clause->length();
//   const Literal* head = (*clause)[0];
//   int headPredicate = head->functor();

//   int firstLiteral;
// //   if (head->isEquality()) {
// //     return;
// //   }
//   if (head->isNegative()) {
//     if (clause->inputType() == Unit::AXIOM) {
//       return;
//     }
//     firstLiteral = 0;
//     str << "g(T):-";
//     goto nonunit;
//   }

//   if (headPredicate != lastPredicate) {
//     lastPredicate = headPredicate;
//     nonUnitFound = false;
//   }

//   if (length == 1) {
//     output(head,str,'p');
//     str << "_).\n";
//     return;
//   }

//   // length >= 1
//   if (! nonUnitFound) {
//     nonUnitFound = true;
//     int pred = head->functor();
//     int arity = head->arity();
//     str << 'p' << pred << '(';
//     for (int i = arity-1;i >= 0;i--) {
//       str << "_,";
//     }
//     str << "0):-!,fail.\n";
//     str << 'p' << pred << '(';
//     for (int i = 0;i < arity;i++) {
//       str << 'X' << i << ',';
//     }
//     str << "T):-T1 is T-1,";
//     str << 'q' << pred << '(';
//     for (int i = 0;i < arity;i++) {
//       str << 'X' << i << ',';
//     }
//     str << "T1).\n";
//   }

//   output(head,str,'q');
//   str << "T):-";

//   if (length == 2) {
//     output((*clause)[1],str,'p');
//     str << "T).\n";
//     return;
//   }

//   firstLiteral = 1;
//  nonunit:
//   Sort<const Literal*,CASC> sort(length-firstLiteral,*this);
//   for (int i = firstLiteral;i < length;i++) {
//     sort.add((*clause)[i]);
//   }
//   sort.sort();
//   for (int i = firstLiteral;i < length;i++) {
//     if (i > firstLiteral) {
//       str << ',';
//     }
//     output(sort[i-firstLiteral],str,'p');
//     str << "T)";
//   }
//   str << ".\n";
// }

// CASC::VarCounter::VarCounter()
//   : Array<const Clause*>(15)
// {
//   CALL("CASC::VarCounter::VarCounter");

//   fillInterval(0,15);
// } // CASC::VarCounter::VarCounter

// void CASC::VarCounter::fillInterval(size_t start,size_t end)
// {
//   CALL("CASC::VarCounter::fillInterval");

//   for (size_t i = start;i < end;i++) {
//     _array[i] = 0;
//   }
// } // CASC::VarCounter::fillInterval

/**
 * Initialize CASC.
 * @since 15/06/2008 Kemerovo
 */
CASC::CASC(ostream& str)
  : _goals(7),
    _stream(str)
{
  CALL("CASC::CASC");

  Signature* sig = env.signature;
  _numberOfHeaders = 2*sig->predicates();
  _occurrences = array_new<int>(
      ALLOC_KNOWN(sizeof(int)*_numberOfHeaders,"CASC:occ"),
      _numberOfHeaders);
  for (int i = _numberOfHeaders-1;i >= 0;i--) {
    _occurrences[i] = 0;
  }

//   for (int i = HOW_MANY-1;i >= 0;i--) {
//     _vars[i] = 0;
//   }
//   for (int i = HOW_MANY-1;i >= 0;i--) {
//     _syms[i] = 0;
//   }
//   for (int i = HOW_MANY-1;i >= 0;i--) {
//     _lits[i] = 0;
//   }

//   Signature* sig = env.signature;
//   _numberOfFunctions = sig->functions();
//   _funs = (int*)ALLOC_UNKNOWN(sizeof(int)*_numberOfFunctions,"CASC::funs");
//   _funClauses = (const Clause**)ALLOC_UNKNOWN(sizeof(Clause*)*_numberOfFunctions,
//  					      "CASC::funClauses");
//   _numberOfHeaders = 2*sig->predicates();
//   _predicates = (Predicate*)ALLOC_UNKNOWN(sizeof(Predicate)*_numberOfHeaders,
//  					  "CASC::preds");
//   for (int i = _numberOfHeaders/2-1;i >= 0;i--) {
//     _predicates[2*i].initialise(sig->predicateArity(i));
//     _predicates[2*i+1].initialise(sig->predicateArity(i));
//   }
//   _predClauses = (const Clause**)ALLOC_UNKNOWN(sizeof(Clause*)*_numberOfHeaders,
//  					       "CASC::predClauses");
} // CASC::CASC

CASC::~CASC()
{
  CALL("CASC::~CASC");

// //   DEALLOC_UNKNOWN(_funs,"CASC::funs");
// //   DEALLOC_UNKNOWN(_funClauses,"CASC::funClauses");
// //   DEALLOC_UNKNOWN(_predClauses,"CASC::predClauses");

// //   cout << "------------------END\n";
// //   Signature* sig = env.signature;
// //   for (int i = _numberOfPredicates;i >= 0;i--) {
// //     Predicate& pred = _predicates[i];
// //     unsigned arity = sig->predicateArity(i);
// //     cout << 'P' << i << ' ' << pred.positiveOccurrences << '/'
// // 	 << pred.negativeOccurrences << ": [";
// //     for (unsigned a = 0;a < arity;a++) {
// //       if (a > 0) {
// // 	cout << ',';
// //       }
// //       cout << pred.getArgumentCounter(a,true) << ':'
// // 	   << pred.getArgumentCounter(a,false);
// //     }
// //     cout << "]\n";
// //     pred.destroy(arity);
// //   }
// //   cout << "------------------END\n";
// //   exit(0);
// //   DEALLOC_UNKNOWN(_predicates,"CASC::preds");
} // CASC::~CASC

/**
 * Scan profile from a problem.
 * @since 15/06/2008 Kemerovo
 */
void CASC::scan(const UnitList* units)
{
  CALL("CASC::scan(UnitList*)");

  // first round: just count the total number of rules
  _numberOfRules = 0;
  UnitList::Iterator uit(units);
  while (uit.hasNext()) {
    Clause* cls = static_cast<Clause*>(uit.next());
    switch (cls->inputType()) {
    case Unit::AXIOM:
    case Unit::ASSUMPTION:
    case Unit::LEMMA:
      _numberOfRules += cls->length();
      break;
    case Unit::CONJECTURE:
      _numberOfRules += cls->length();
      _goals.push(cls);
      break;
    }
  }

  ASS(_numberOfRules > 0);

  cout << "% Rules: " << _numberOfRules << "\n";
  cout << "% Goals: " << _goals.length() << "\n";

  _rules = array_new<Rule>(
      ALLOC_KNOWN(sizeof(Rule)*_numberOfRules,"CASC::RuleArray"),
      _numberOfRules);
  int r = 0;
  // compiling rules
  UnitList::Iterator uit1(units);
  while (uit1.hasNext()) {
    Clause& cls = *static_cast<Clause*>(uit1.next());
    for (int i = cls.length()-1;i >= 0;i--) {
      Rule& rule = _rules[r];
      rule.clause=&cls;
      const Literal* lit = cls[i];
//       cout << _occurrences[lit->header()]++ << "\n";
      rule.literal=lit;
      r++;
    }
  }

  sort(_rules,0,_numberOfRules-1);

  _stream << ":- set_prolog_flag(occurs_check,true).\n"
	  << ":- style_check(-singleton).\n";
  Rule* rule = _rules;
  Rule* lastRule = _rules + _numberOfRules;
  while (rule != lastRule) {
    outputRule(rule);
    rule++;
  }
  outputEqualityRules();

  while (! _goals.isEmpty()) {
    outputGoal(static_cast<const Clause*>(_goals.pop()));
  }

  _stream << "gg :- gg(0).\n"
// 	  << "gg(N) :- write('%   '),writeln(N), goal(Gs), solve(Gs,N,[g(Gs)],P), writeln('% PROVED %\n%'), writeln(P), !, halt.\n"
	  << "gg(N) :- write('%   '),writeln(N), goal(Gs,A), solve(Gs,N,[A],P), write('% PROVED '), write_proof(P), writeln(''), !, halt.\n"
	  << "gg(N) :- N1 is N+1,gg(N1).\n"
	  << "write_proof([P]) :- write(P),!.\n"
	  << "write_proof([P|Ps]) :- write(P),write(','),write_proof(Ps),!.\n"
	  << "solve([],_,P,P) :- !.\n"
	  << "solve(Fs,N,P1,P4) :- select(Fs,G,Gs), N > 0,c(G,Hs,A), N1 is N-1, solve(Hs,N1,P1,P2), solve(Gs,N,P2,P3),P4=[A|P3].\n"
	  << "select([G],G,[]) :- !.\n"
	  << "select(Gs,H,Hs) :- select_best(Gs,H,Hs,_,_).\n"
	  << "select_ground([G|Gs],G,Gs) :- ground(G), !.\n"
	  << "select_ground([G|Gs],H,[G|Hs]) :- select_ground(Gs,H,Hs).\n"
	  << "select_best([G],G,[],V,N) :- !, count(G,V,N).\n"
	  << "select_best([G|Gs],H,Hs,V,N) :- !, count(G,V1,N1), select_best(Gs,F,Fs,V2,N2), select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs).\n"
	  << "select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs) :- (V1 < V2; V1 == V2,N1 >= N2), !, H=G,Hs=Gs,V=V1,N=N1.\n"
	  << "select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs) :- H=F,Hs=[G|Fs],V=V2,N=N2.\n"
	  << "count(T,V,N) :- count(T,0,0,V,N).\n"
	  << "count(X,V,N,V1,N) :- var(X), !, V1 is V+1.\n"
	  << "count(T,V,N,V1,N2) :- functor(T,_,A),count(T,A,V,N,V1,N1), N2 is N1+1.\n"
	  << "count(_,0,V,N,V,N) :- !.\n"
	  << "count(T,A,V,N,V2,N2) :- arg(A,T,TA), count(TA,V,N,V1,N1), A1 is A-1, count(T,A1,V1,N1,V2,N2).\n";

// 	  << "select([G],G,[]) :- !.\n"
// 	  << "select([G|Gs],G,Gs) :- ground(G), !.\n"
// 	  << "select([G|Gs],H,[G|Hs]) :- select(Gs,H,Hs).\n";

//   UnitList::Iterator us(units);
//   int numberOfClauses = 0;
//   while (us.hasNext()) {
//     numberOfClauses++;
//     scan(static_cast<const Clause*>(us.next()));
//   }

//   for (unsigned p = 0;p < _numberOfHeaders;p++) {
//     if (_predicates[p].occurrences) {
//       continue;
//     }
//     cout << 'p' << p << '(';
//     for (int i = sig->predicateArity(p/2)-1;i >= 0;i--) {
//       cout << "_,";
//     }
//     cout << "_):-!,fail.\n";
//   }

//  Sort<Clause*,CASC> sort(numberOfClauses,*this);
//   // evaluate clauses and count the number of clauses that can be used at all
//   UnitList::Iterator vs(units);
//   int useful = 0;
//   while (vs.hasNext()) {
//     Clause* c = static_cast<Clause*>(vs.next());
//     int w = evaluate(c);
//     c->setAge(w);

//     if (w != -1 || c->inputType() != Unit::AXIOM) {
//       useful++;
//       sort.add(c);
//     }
//   }

//   sort.sort();
//   for (int i = 0;i < useful;i++) {
// //     cout << sort[i]->toString() << ' ' << sort[i]->age() << "\n";
//     output(sort[i],cout);
//   }
//   cout << "main:-gg(0).\n"
//           "gg(T):-writeln(T),g(T),writeln('yes!'),halt.\n"
//           "gg(T):-T1 is T+1,gg(T1).\n";
} // CASC::scan(const UnitList* units)

void CASC::outputEqualityRules()
{
  _stream << "c(p1(X,X),[],-1).\n"
	  << "c(p1(X,Y),[p1(Y,X)],-1).\n"
	  << "c(p1(X,Y),[p1(X,Z), p1(Z,Y)],-1).\n";
}

/**
 * Write the string "X1,...,Xm".
 */
void CASC::writeVars(int m)
{
  ASS(m > 0);

  for (int i = 1;i < m;i++) {
    _stream << 'X' << i << ',';
  }
  _stream << 'X' << m;
} // CASC::writeVars

void CASC::outputRule(const Rule* rule)
{
  const Literal* lit = rule->literal;
  const Clause* cls = rule->clause;

  _stream << "c(";
  outputLiteral(true,lit);
  _stream << ",[";
  int length = cls->length();
  bool first = true;
  for (int i = 0;i < length;i++) {
    const Literal* m = (*cls)[i];
    if (m == lit) {
      continue;
    }
    if (! first) {
      _stream << ", ";
    }
    else {
      first = false;
    }
    outputLiteral(false,m);
  }
  _stream << "]," << cls->adam() << ").\n";
}

void CASC::outputGoal(const Clause* cls)
{
  _stream << "goal([";
  int length = cls->length();
  bool first = true;
  for (int i = 0;i < length;i++) {
    const Literal* m = (*cls)[i];
    if (! first) {
      _stream << ", ";
    }
    else {
      first = false;
    }
    outputLiteral(false,m);
  }
  _stream << "]," << cls->adam() << ").\n";
}

void CASC::outputLiteral(bool head,const Literal* literal)
{
  char prefix;
  if (literal->isPositive()) {
    if (head) {
      prefix = 'p';
    }
    else {
      prefix = 'n';
    }
  }
  else if (head) {
    prefix = 'n';
  }
  else {
    prefix = 'p';
  }
//   _stream << '\'' << prefix << env.signature->predicateName(literal->functor()) << '\'';
  _stream << prefix << literal->functor();
  outputArgs(literal->args());
} // CASC::outputLiteral

void CASC::outputArgs(const TermList* args)
{
  if (args->isEmpty()) {
    return;
  }
  _stream << '(';
  outputArg(args);
  args = args->next();
  while (! args->isEmpty()) {
    _stream << ',';
    outputArg(args);
    args = args->next();
  }
  _stream << ')';
}

void CASC::outputArg (const TermList* arg)
{
  if (arg->isVar()) {
    _stream << 'X' << arg->var();
    return;
  }

  const Term* t = arg->term();
  _stream << 'f' << t->functor();
  outputArgs(t->args());
} // CASC::outputArg


/**
 * Sorting an array of LRule between and inclusive of indexes p and r.
 * Copied from the generic Sort module for efficiency
 * @since 03/08/2008 Torrevieja
 */
void CASC::sort(Rule* rules,int p,int r)
{
  CALL("CASC::Sort::sort(Rule*,...)");

  if (p >= r) {
    return;
  }
  int m = (p+r)/2;
  int i = p;
  int j = r;
  Rule a = rules[m];
  while (i < m) {
    Rule b = rules[i];
    if (compare(a,b) != -1) { // a[i] <= a[m]
      i++;
      continue;
    }
    if (m < j) {
      rules[i] = rules[j];
      rules[j] = b;
      j--;
      continue;
    }
    rules[m] = b;
    rules[i] = rules[m-1];
    m--;
    j--;
  }
  while (m < j) {
    Rule b = rules[j];
    if (compare(b,a) != -1) { // a[m] <= a[j]
      j--;
      continue;
    }
    rules[m] = b;
    rules[j] = rules[m+1];
    m++;
  }
  rules[m] = a;
  sort(rules,p,m-1);
  sort(rules,m+1,r);
} // CASC::sort

/**
 * Compare the literal headers.
 * @since 03/08/2008 Torrevieja
 */
int CASC::compare(const Rule& r1,const Rule& r2)
{
  unsigned h1 = r1.literal->header();
  unsigned h2 = r2.literal->header();
  if (h1 < h2) {
    return -1;
  }
  if (h1 > h2) {
    return 1;
  }
  unsigned l1 = r1.clause->length();
  unsigned l2 = r2.clause->length();

  return l1 < l2 ? -1 : l1 > l2 ? 1 : 0;
} // compare

// /**
//  * Scan a clause.
//  * @since 15/06/2008 Kemerovo
//  */
// void CASC::scan (const Clause* clause)
// {
//   CALL("CASC::scan (const Clause*)");

//   _varsInThisClause = 0;
//   _symsInThisClause = 0;
//   _currentClause = clause;

//   int length = clause->length();
//   for (int i = length-1;i >= 0;i--) {
//     const Literal* lit = (*clause)[i];
//     scan(lit);
//     if (i != 0 && lit->isPositive()) { // the literal is positive and not first
//       // make it first
//       (*clause)[i] = (*clause)[0];
//       (*clause)[0] = lit;
//     }
//   }

//   if (_varsInThisClause < HOW_MANY-1) {
//     _vars[_varsInThisClause]++;
//   }
//   else {
//     _vars[HOW_MANY-1]++;
//   }
//   if (_symsInThisClause < HOW_MANY-1) {
//     _syms[_symsInThisClause]++;
//   }
//   else {
//     _syms[HOW_MANY-1]++;
//   }
//   if (length < HOW_MANY-1) {
//     _lits[length]++;
//   }
//   else {
//     _lits[HOW_MANY-1]++;
//   }
// } // CASC::scan (const Clause* clause, bool isAxiom)


// /**
//  * Scan a literal.
//  * @since 15/06/2008 Kemerovo
//  */
// void CASC::scan (const Literal* lit)
// {
//   CALL("CASC::scan (const Literal*...)");

//   Predicate& pred = _predicates[lit->functor()];
//   bool positive = lit->isPositive();
//   if (positive) {
//     pred.positiveOccurrences++;
//   }
//   else {
//     pred.negativeOccurrences++;
//   }

//   int argNumber = 0;
//   for (const TermList* ts = lit->args(); ! ts->isEmpty(); ts = ts->next()) {
//     if (ts->isVar()) {
//       pred.incrementArgumentCounter(argNumber,positive,1);
//     }
//     argNumber++;
//   }

//   if (_predClauses[lit->functor()] != _currentClause) {
//     _predClauses[lit->functor()] = _currentClause;
//     _symsInThisClause++;
// //     if (lit->isEquality()) {
// //       cout << _currentClause->toString() << "\n";
// //     }
//   }
//   scan(lit->args());
// } // CASC::scan (const Atom& term, bool& isGround)

// /**
//  * Scan a term arguments.
//  * @since 15/06/2008 Kemerovo
//  */
// void CASC::scan(const TermList* ts)
// {
//   CALL("CASC::scan(TermList*))");

//   Stack<const TermList*> stack(64);

//   for (;;) {
//     if (ts->isEmpty()) {
//       if (stack.isEmpty()) {
// 	return;
//       }
//       ts = stack.pop();
//     }
//     // ts is non-empty
//     if (ts->isVar()) {
//       int v = ts->var();
//       if (vc[v] != _currentClause) {
// 	vc[v] = _currentClause;
// 	_varsInThisClause++;
//       }
//     }
//     else { // ts is a reference to a complex term
//       const Term* t = ts->term();
// //       _funs[t->functor()]++;
// //       if (_funClauses[t->functor()] != _currentClause) {
// // 	_funClauses[t->functor()] = _currentClause;
// // 	_symsInThisClause++;
// //       }
//       const TermList* ss = t->args();
//       if (! ss->isEmpty()) {
// 	stack.push(ss);
//       }
//     }
//     ts = ts->next();
//   }
// } // CASC::scan (const TermList*)


// /**
//  * Output the profile to a string readable by a human. NOT ALL FIELDS
//  * ARE CURRENTLY OUTPUT.
//  * @since 15/06/2008 Kemerovo
//  */
// string CASC::toString () const
// {
//   string result("");

//   result += (string)"Variables\n";
//   for (int i = 0; i < HOW_MANY-1;i++) {
//     result += string("  ") + Int::toString(i) + ':'
//       + Int::toString(_vars[i]) + '\n';
//   }
//   result += string(" >") + Int::toString(HOW_MANY-2) + ':'
//     + Int::toString(_vars[HOW_MANY-1]) + '\n';

//   result += (string)"Symbols\n";
//   for (int i = 0; i < HOW_MANY-1;i++) {
//     result += string("  ") + Int::toString(i) + ':'
//       + Int::toString(_syms[i]) + '\n';
//   }
//   result += string(" >") + Int::toString(HOW_MANY-2) + ':'
//     + Int::toString(_syms[HOW_MANY-1]) + '\n';

//   result += (string)"Literals\n";
//   for (int i = 0; i < HOW_MANY-1;i++) {
//     result += string("  ") + Int::toString(i) + ':'
//       + Int::toString(_lits[i]) + '\n';
//   }
//   result += string(" >") + Int::toString(HOW_MANY-2) + ':'
//     + Int::toString(_lits[HOW_MANY-1]) + '\n';

//   Signature* sig = env.signature;

//   result += "Functions with more than 10 occurrences:\n";
//   int fn = sig->functions();
// //   for (int i = fn-1;i >= 0;i--) {
// //     if (_funs[i] > 10) {
// //       result += string("  ") + Int::toString(_funs[i]) + ": " +
// // 	sig->functionName(i) + '\n';
// //     }
// //   }
//   result += "Predicates with more than 10 occurrences:\n";
//   int pd = sig->predicates();
//   for (int i = pd-1;i >= 0;i--) {
//     int pos = _predicates[i].positiveOccurrences;
//     int neg = _predicates[i].negativeOccurrences;
//     if (pos < 2 || neg < 2 || pos+neg > 10) {
//       result += string("  ") + Int::toString(pos) + '/' + Int::toString(neg)
// 	+ ": " + sig->predicateName(i) + '\n';
//     }
//   }

//   return result;
// } // CASC::toString

// /**
//  * Evaluate the clause.
//  * @return the following value:
//  * <ul>
//  * <li>-1 if it has no positive literals and is non-goal (such clauses
//  * should be discarded);</li>
//  * <li>0 if the clause is unit;</li>
//  * <li>product, over all negative literals in it, of the number of
//  * positive occurrences of the predicate of this literal.</li>
//  * </ul>
//  * @since 15/06/2008 Kemerovo
//  */
// int CASC::evaluate(const Clause* c)
// {
//   CALL("CASC::evaluate");

//   bool hasPos = false;
//   int length = c->length();
//   int product = 1;
//   for (int i = length-1;i >= 0;i--) {
//     const Literal* lit = (*c)[i];
//     if (lit->isPositive()) {
//       hasPos = true;
//     }
//     else {
//       int prod = product * _predicates[lit->functor()].positiveOccurrences;
//       if (prod != 0 && prod < product) { // overflow
// 	return INT_MAX;
//       }
//       product = prod;
//     }
//   }
//   if (! hasPos) {
//     return -1;
//   }
//   if (length == 1) {
//     return 0;
//   }

//   if (product == 0) {
//     return 1; // this clause should be discarded as well
//   }
//   return product+1;
// } // CASC::evaluate

// /**
//  * Compare two clauses using their ages.
//  * @since 27/06/2008 Manchester
//  */
// bool CASC::lessThan(const Clause* c1,const Clause* c2)
// {
//   int pred1 = (*c1)[0]->functor();
//   int pred2 = (*c2)[0]->functor();
//   if (pred1 < pred2) {
//     return true;
//   }
//   if (pred2 < pred1) {
//     return false;
//   }
//   return c1->age() < c2->age();
// } // CASC::lessThan

// /**
//  * Compare two literals using (1) the number of occurrences of their
//  * predicate in the problem; (2) weight.
//  * @since 28/06/2008 Manchester
//  */
// bool CASC::lessThan(const Literal* lit1,const Literal* lit2)
// {
//   int occ1 = _predicates[lit1->functor()].positiveOccurrences;
//   int occ2 = _predicates[lit2->functor()].positiveOccurrences;
//   if (occ1 < occ2) {
//     return true;
//   }
//   if (occ2 < occ1) {
//     return false;
//   }
//   return lit1->weight() < lit2->weight();
// } // CASC::lessThan

/**
First literal selection:
   << "select([G|Gs],G,Gs).\n";


Simple ground-first selection
select([G],G,[]) :- !.
select([G|Gs],G,Gs) :- ground(G), !.
select([G|Gs],H,[G|Hs]) :- select(Gs,H,Hs).

Fewer variable occurrences selection:
Count counts non-variables and variables in term

select([G],G,[]) :- !.
select(Gs,H,Hs) :- select_best(Gs,H,Hs,_,_).

select_ground([G|Gs],G,Gs) :- ground(G), !.
select_ground([G|Gs],H,[G|Hs]) :- select_ground(Gs,H,Hs).

select_best([G],G,[],V,N) :- !, count(G,V,N).
select_best([G|Gs],H,Hs,V,N) :- !, count(G,V1,N1),
                                   select_best(Gs,F,Fs,V2,N2),
                                   select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs).
select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs) :- (V1 < V2; V1 == V2,N1 >= N2), !,
                                               H=G,Hs=Gs,V=V1,N=N1.
select_best(V1,V2,V,N1,N2,N,G,F,H,Gs,Fs,Hs) :- H=F,Hs=[G|Fs],V=V2,N=N2.

count(T,V,N) :- count(T,0,0,V,N).
count(X,V,N,V1,N) :- var(X), !, V1 is V+1.
count(T,V,N,V1,N2) :- functor(T,_,A),count(T,A,V,N,V1,N1), N2 is N1+1.

count(_,0,V,N,V,N) :- !.
count(T,A,V,N,V2,N2) :- arg(A,T,TA), count(TA,V,N,V1,N1), A1 is A-1, count(T,A1,V1,N1,V2,N2).

 */
