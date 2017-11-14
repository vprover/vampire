
/*
 * File ClauseFlattening.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
