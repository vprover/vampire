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
 * Defines definition-reuse policies, configured by an option
 */

#include "NameReuse.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Shell/Rectify.hpp"
#include <iostream>

namespace Shell {

NameReuse *NameReuse::skolemInstance()
{
  CALL("NameReuse::skolemInstance");
  static NameReuse *instance = new NameReuse();
  return instance;
}

NameReuse *NameReuse::definitionInstance()
{
  CALL("NameReuse::definitionInstance");
  static NameReuse *instance = new NameReuse();
  return instance;
}

Formula *NameReuse::normalise(Formula *f)
{
  CALL("NameReuse::normalise");
  //std::cout << "normalise: " << f->toString() << std::endl;
  Rectify rectify;
  return rectify.rectify(f);
}

bool NameReuse::get(Formula *normalised, unsigned &symbol)
{
  CALL("NameReuse::get");
  //std::cout << "get: " << normalised->toString() << std::endl;
  return _map.find(normalised->toString(), symbol);
  /*
  if(_map.find(normalised->toString(), symbol)) {
    std::cout << "hit: " << normalised->toString() << std::endl;
    return true;
  }
  return false;
  */
}

void NameReuse::put(Formula *normalised, unsigned symbol)
{
  CALL("ExactNameReuse::put");
  //std::cout << "put: " << env.signature->functionName(symbol) << " for " << normalised->toString() << std::endl;
  _map.insert(normalised->toString(), symbol);
}

}; // namespace Shell