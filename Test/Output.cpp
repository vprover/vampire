/**
 * @file Output.cpp
 * Implements class Output for writing various data structures in the
 * Prolog format
 * @since 25/04/2008 flight Frankfurt-Vienna
 */

#include "../Debug/Assertion.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"
#include "../Lib/Int.hpp"
#include "Output.hpp"

using namespace std;
using namespace Kernel;
using namespace Test;

/**
 * Convert a term to a prolog string.
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
string Output::toString(const Term* t)
{
  CALL("Output::toString(const Term*)");
  if (t->arity() == 0) {
    return string("c") + Int::toString(t->functor());
  }
  return string("f") + Int::toString(t->functor()) +
         "(" + toString(t->args()) + ")";
} // Output::toString(const Term* t)

/**
 * Convert a term list to a prolog string.
 * @since 25/04/2008 flight Frankfurt-Vienna
 */
string Output::toString(const TermList* ts)
{
  CALL("Output::toString(const TermList*)");

  string r("");
  for (;;)  {
    if (ts->isVar()) {
      r += "X";
      r += Int::toString(ts->var()); 
    }
    else {
      r += toString(ts->term());
    }
    ts = ts->next();
    if (ts->isEmpty()) {
      return r;
    }
    r += ',';
  }
} // Output::toString(const TermList* t)

/**
 * Convert a literal to a prolog string.
 * @since 26/04/2008 Vienna
 */
string Output::toString(const Literal* l)
{
  CALL("Output::toString(const Literal*)");

  string tt(l->isPositive() ? "p(" : "n(" );
  tt += l->isEquality() ? "e" : "p" + Int::toString(l->functor());
  if (l->arity() != 0) {
    tt += "(" + toString(l->args()) + ")";
  }
  return tt + ')';
} // Output::toString(const Literal* l)

/**
 * Convert a clause to a prolog string.
 * @since 26/04/2008 Vienna
 */
string Output::toString(const Clause* c)
{
  CALL("Output::toString(const Clause*)");

  string r("c(" + Int::toString(c->number()) + ",[");

  int last = c->length() - 1;
  for (int i = 0;i <= last; i++) {
    r += toString((*c)[i]);
    if (i != last) {
      r += ',';
    }
  }
  return r + "])";
} // Output::toString(const Clause*)

