/**
 * @file ClauseFlattening
 * Defines class ClauseFlattening
 */ 

#ifndef __ClauseFlattening__
#define __ClauseFlattening__

#include "Forwards.hpp"
#include "Kernel/Clause.hpp"

namespace FMB {

using namespace Kernel;

class ClauseFlattening 
{
public:

  static Clause* flatten(Clause* c);

private:
  static bool isShallow(Literal* lit);

  // Get rid of negative inequalities x!=y among variables
  static Clause* resolveNegativeVariableEqualities(Clause* cl);

};


}

#endif // __ClauseFlattening__
