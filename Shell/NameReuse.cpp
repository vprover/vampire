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
 * @file NameReuse.cpp
 * Attempt to reuse names introduced to represent formulae, e.g. Skolems or naming
 */

#include "NameReuse.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Lib/ScopedPtr.hpp"

namespace Shell {

NameReuse *NameReuse::skolemInstance()
{
  CALL("NameReuse::skolemInstance");
  static ScopedPtr<NameReuse> instance(new NameReuse());
  return instance.ptr();
}

NameReuse *NameReuse::definitionInstance()
{
  CALL("NameReuse::definitionInstance");
  static ScopedPtr<NameReuse> instance(new NameReuse());
  return instance.ptr();
}

// generate key for only this term and not its subterms
void NameReuse::key(vstringstream &buf, TermList ts)
{
  CALL("NameReuse::key(vstringstream &, TermList)");
  if(ts.isVar())
    // need to rename variables occuring in terms, sorts
    buf << 'x' << _renaming.getOrBind(ts.var());
  else
    // all functors realised as fN, where N is the functor's index
    // sorts are known to be sorts from their context, so this is OK
    // as there is exactly one function arity per symbols, don't need parentheses
    buf << 'f' << ts.term()->functor();
}

// generate key only for the subterms
void NameReuse::key(vstringstream &buf, Term *t)
{
  CALL("NameReuse::key(vstringstream &, Term *)");
  SubtermIterator subterms(t);
  while(subterms.hasNext())
    key(buf, subterms.next());
}

// generate a "key" for `f` that identifies it up to alpha-equivalence
// assumes that `f` has been rectified at some point
// looks a bit like `toString()`, but more compact and necessarily has some differences
vstring NameReuse::key(Formula *f)
{
  CALL("NameReuse::key(Formula *)");
  //std::cout << "key for: " << f->toString() << std::endl;
  vstringstream buf;
  // reset the canonical renaming for this formula
  // variables will be renamed in order of traversal
  _renaming.reset();

  // depth-first traversal of `f`
  Kernel::SubformulaIterator subformulae(f);
  while(subformulae.hasNext()) {
    Formula *subformula = subformulae.next();
    Connective connective = subformula->connective();
    switch(connective) {
      // literals are basically terms for our purposes
      case LITERAL: {
        Literal *l = subformula->literal();
        if (!l->polarity())
          buf << '~';
        buf << 'p' << l->functor();
        key(buf, l);

        // special case: if we have X = Y, can't work out what sort '=' is applied to from context
        if(l->isTwoVarEquality()) {
          // luckily, we already keep it, so add it after the variables
          TermList sort = l->twoVarEqSort();
          key(buf, sort);
          if (sort.isTerm())
            key(buf, sort.term());
        }
        break;
      }
      // AND and OR have a variable number of subformulae, so include that information
      case AND:
        buf << '&' << FormulaList::length(subformula->args());
        break;
      case OR:
        buf << '|' << FormulaList::length(subformula->args());
        break;
      // other connectives have a known number of subformulae
      // probably shouldn't get here: we expect ENNF
      case IMP:
        buf << '>';
        break;
      case XOR:
        buf << '+';
        break;
      case IFF:
        buf << '=';
        break;
      // probably shouldn't get here: we expect ENNF
      case NOT:
        buf << '~';
        break;
      // FORALL AND EXISTS: need to include bound variables
      case FORALL:
      case EXISTS:
      {
        buf << (connective == FORALL ? '!' : '?');
        // no sorts required for bound variables, can infer sort from where they are used
        // unless they're not used, but in that case it's OK anyway
        VList::Iterator vars(subformula->vars());
        while(vars.hasNext())
          buf << 'x' << _renaming.getOrBind(vars.next());
        break;
      }
      case BOOL_TERM:
      {
        buf << 'b';
        TermList boolean = subformula->getBooleanTerm();
        key(buf, boolean);
        if(boolean.isTerm())
          key(buf, boolean.term());
        break;
      }
      case TRUE:
        buf << 't';
        break;
      case FALSE:
        buf << 'f';
        break;
      // shouldn't happen
      case NAME:
        buf << 'n' << static_cast<NamedFormula *>(subformula)->name();
        break;
      case NOCONN:
        ASSERTION_VIOLATION;
    }
  }

  vstring key = buf.str();
  //std::cout << "is: " << key << std::endl;
  return key;
}

bool NameReuse::get(const vstring &key, unsigned &symbol)
{
  CALL("NameReuse::get");
  //std::cout << "get: " << key << std::endl;
  return _map.find(key, symbol);
  /*
  if(_map.find(key, symbol)) {
    std::cout << "hit: " << key << std::endl;
    return true;
  }
  return false;
  */
}

void NameReuse::put(vstring key, unsigned symbol)
{
  CALL("NameReuse::put");
  //std::cout << "put: " << symbol << " for " << key << std::endl;
  _map.insert(key, symbol);
}

VirtualIterator<unsigned> NameReuse::freeVariablesInKeyOrder(Formula *f)
{
  CALL("NameReuse::freeVariablesInKeyOrder");
  return pvi(FormulaVarIterator(f));
}

}; // namespace Shell