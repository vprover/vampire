/**
 * @file Rule/Prolog.cpp
 * Implements class Prolog for compiling a rule index into a Prolog program.
 * @since 08/08/2008 flight Singapore-Sydney
 */

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "Prolog.hpp"

using namespace std;
using namespace Rule;

/**
 * Compile the index to a Prolog program and write it to the stream.
 * @since 08/08/2008 flight Singapore-Sydney
 */
void Prolog::write(Index& index)
{
  CALL("Prolog::write-1");

  _index = &index;

  // first, write all rules
  int r = index.numberOfRules();
  const Rule* rules = index.rules();
  for (int i = 0;i < r;i++) {
    writeRule(i,rules[i]);
  }

  write(index.headers(),index.entries());
} // class Prolog

void Prolog::writeRule(int ruleNumber,const Rule& rule)
{
  CALL("Prolog::writeRule");

  const Clause* clause = rule.clause;
  const Literal* literal = rule.literal;

  _stream << "rl(" << ruleNumber << ',';
  outputLiteral(false,literal);
  _stream << ",[";
  bool first = true;
  for (unsigned i = 0;i < clause->length();i++) {
    const Literal* lit = (*clause)[i];
    if (lit == literal) {
      continue;
    }
    if (! first) {
      _stream << ", ";
    }
    else {
      first = false;
    }
    outputLiteral(true,lit);
  }
  // TAIL
  _stream << "]) :- !.\n";
} // Prolog::writeRule

/**
 * Compile the top-level list of entries to a Prolog program and
 * write it to the stream.
 * @since 08/08/2008 flight Singapore-Sydney
 */
void Prolog::write(int headers,const Index::Entry* entries)
{
  CALL("Prolog::write-2");

  for (int h = 0;h < headers;h++) {
    const Index::Entry& entry = entries[h];
    if (entry.rules == 0) {
      continue;
    }
    int polarity = Literal::headerToPolarity(h);
    int predicate = Literal::headerToPredicateNumber(h);

    unsigned arity = entry.arity;
    int entryNumber = _entryEnumerator.add(&entry);

    _stream << "retrieve(" << (polarity ? 'n' : 'p') << predicate << '(';
    if (arity > 0) {
      writeVars(arity);
      _stream << ',';
    }
    _stream << "N,S)) :- !,r" << entryNumber << '(';
    if (arity > 0) {
      writeVars(arity);
      _stream << ',';
    }
    _stream << "0,[],N,S).\n";
  }
  for (int h = 0;h < headers;h++) {
    write(entries+h);
  }
} // write

/**
 * Compile the code for a single entry.= and write it to the stream.
 * @since 08/08/2008 flight Singapore-Sydney
 */
void Prolog::write(const Index::Entry* entry)
{
  CALL("Prolog::write-3");

  unsigned arity = entry->arity;
  unsigned rules = entry->rules;
  int entryNumber = _entryEnumerator.add(entry);

  switch (arity) {
  case 0:
    _stream << "r" << entryNumber << '(';
    _stream << ",M,P,N,S) :- N is M+" << rules << ", "
	    << "S=[leaf(" << entryNumber << "),P].\n";
    writeLeaf(entryNumber,entry);
    break;
  case 1:
    _stream << "r" << entryNumber << '(';
    writeVars(1);
    _stream << ",M,P,N,S) :- ";
    _stream << 'r' << entryNumber << "_" << 1 << "(X1,M,P,N,S).\n";
    break;
  default:
    _stream << "r" << entryNumber << '(';
    writeVars(arity);
    _stream << ",M,P,N,S) :- ";
    for (unsigned i = 1;i <= arity;i++) {
      _stream << 'r' << entryNumber << "_" << i << "(X" << i << ",M,P,N"
	      << i << ",S" << i << "), ";
    }
    _stream << "max([";
    for (unsigned i = 1;i <= arity;i++) {
      if (i != 1) {
	_stream << ',';
      }
      _stream << 'N' << i;
    }
    _stream << "],[";
    for (unsigned i = 1;i <= arity;i++) {
      if (i != 1) {
	_stream << ',';
      }
      _stream << 'S' << i;
    }
    _stream << "],N,S).\n";
    break;
  }
} // write

/**
 * Write the string "X1,...,Xm".
 */
void Prolog::writeVars(int m)
{
  ASS(m > 0);

  for (int i = 1;i < m;i++) {
    _stream << 'X' << i << ',';
  }
  _stream << 'X' << m;
} // Prolog::writeVars


int Prolog::Enumerator::add(const Index::Entry* entry)
{
  int result;
  if (find(entry,result)) {
    return result;
  }
  insert(entry,_nextNumber++);
  return _nextNumber-1;
} // Prolog::Enumerator::insert

void Prolog::outputLiteral (bool preservePolarity,const Literal* literal)
{
  bool pos = literal->isPositive();
  if (! preservePolarity) {
    pos = ! pos;
  }
  _stream << (pos ? 'p' : 'n') << literal->functor();
  outputArgs(literal->args());
} // Prolog::outputLiteral

void Prolog::outputArgs(const TermList* args)
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

void Prolog::outputArg (const TermList* arg)
{
  if (arg->isVar()) {
    _stream << 'Y' << arg->var();
    return;
  }

  const Term* t = arg->term();
  _stream << 'f' << t->functor();
  outputArgs(t->args());
} // Prolog::outputArg

void Prolog::writeLeaf(int entryNumber,const Index::Entry* leafEntry)
{
  CALL("Prolog::writeLeaf");

  ASS(leafEntry->arity == 0);

  const Rule* allRules = _index->rules();
  const Rule** rules = leafEntry->leaf;
  cerr << (void*)&leafEntry << ' ' << leafEntry->rules << "\n";
  for (int i = leafEntry->rules-1;i >= 0;i--) {
    const Rule* rule = rules[i];
    int ruleNumber = rule - allRules;
    _stream << "leaf(" << entryNumber << ',' << ruleNumber << ").\n";
  }
} // Prolog::writeRule
