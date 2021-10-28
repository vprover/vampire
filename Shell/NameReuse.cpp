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
  // std::cout << "put: " << env.signature->functionName(symbol) << " for " << key << std::endl;
  _map.insert(key, symbol);
}

Lib::Stack<unsigned> NameReuse::freeVariablesInKeyOrder(Formula *f)
{
  CALL("NameReuse::freeVariablesInKeyOrder");
  return Lib::Stack<unsigned>::fromIterator(FormulaVarIterator(f));
}

}; // namespace Shell