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
#include "Kernel/FormulaVarIterator.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"
#include "Shell/Rectify.hpp"

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

vstring NameReuse::key(Formula *f)
{
  CALL("NameReuse::key");
  //std::cout << "key for: " << f->toString() << std::endl;
  Rectify rectify;
  Formula *rectified = rectify.rectify(f);
  vstring key = rectified->toString();
  // the function could stop here, but some functions are ad-hoc polymorphic
  // consider:
  // ![X: $int] ?[Y]: (p(Y) & $less(X, X))
  // ![X: $real] ?[Y]: (p(Y) & $less(X, X))
  // therefore: append sort information to free variables to the key
  FormulaVarIterator freeVars(rectified);
  while(freeVars.hasNext()) {
    unsigned free = freeVars.next();
    TermList sort;
    if(SortHelper::tryGetVariableSort(free, rectified, sort)) {
      key.append("#");
      key.append(Int::toString(free));
      key.append(sort.term()->toString());
    }
  }
  //std::cout << "is: " << key << std::endl;
  return key;
}

VTHREAD_LOCAL static DHMap<Signature::Symbol *, unsigned> symbol2index;

bool NameReuse::get(const vstring &key, unsigned &index)
{
  CALL("NameReuse::get");
  //std::cout << "get: " << key << std::endl;
  Signature::Symbol *cached;

  // no reuse
  if(!_map.find(key, cached))
    return false;

  // reuse symbol from this thread
  if(symbol2index.find(cached, index))
    return true;

#if VTHREADED
  // reuse symbol from another thread
  if(cached->skolem()) {
    index = env->signature->functions();
    env->signature->importFunction(cached->clone());
    ALWAYS(symbol2index.insert(cached, index));
  }
  else {
    index = env->signature->predicates();
    env->signature->importPredicate(cached->clone());
    ALWAYS(symbol2index.insert(cached, index));
  }
  return true;
#else
  return false;
#endif
}

void NameReuse::put(vstring key, unsigned index, Signature::Symbol *symbol)
{
  CALL("NameReuse::put");
  //std::cout << "put: " << symbol->name() << " for " << key << std::endl;
#if VTHREADED
  symbol = symbol->clone();
#endif
  ALWAYS(_map.insert(key, symbol));
  ALWAYS(symbol2index.insert(symbol, index));
}

VirtualIterator<unsigned> NameReuse::freeVariablesInKeyOrder(Formula *f)
{
  CALL("NameReuse::freeVariablesInKeyOrder");
  return pvi(FormulaVarIterator(f));
}

}; // namespace Shell