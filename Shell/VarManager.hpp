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
 * @file VarManager.hpp
 * Defines class VarManager.
 */

#ifndef __VarManager__
#define __VarManager__

#include "Lib/VString.hpp"

#include "Forwards.hpp"

namespace Shell {

using namespace std;
using namespace Lib;

class VarManager {
public:
  struct VarFactory
  {
    virtual unsigned getVarAlias(unsigned var) = 0;
    virtual vstring getVarName(unsigned var) = 0;
  };

  static bool varNamePreserving() { return _fact; }
  static void setVarNamePreserving(VarFactory* f) { _fact = f; }
  static VarFactory* varNamePreservingFactory() { return _fact; }

  static unsigned getVarAlias(unsigned var);
  static vstring getVarName(unsigned var);
private:
  static VarFactory* _fact;
};

}

#endif // __VarManager__
