/**
 * @file VarManager.hpp
 * Defines class VarManager.
 */

#ifndef __VarManager__
#define __VarManager__

#include <string>

#include "Forwards.hpp"

namespace Shell {

using namespace std;
using namespace Lib;

class VarManager {
public:
  struct VarFactory
  {
    virtual unsigned getVarAlias(unsigned var) = 0;
    virtual string getVarName(unsigned var) = 0;
  };

  static bool varNamePreserving() { return _fact; }
  static void setVarNamePreserving(VarFactory* f) { _fact = f; }

  static unsigned getVarAlias(unsigned var);
  static string getVarName(unsigned var);
private:
  static VarFactory* _fact;
};

}

#endif // __VarManager__
