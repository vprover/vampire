
/*
 * File ExtensionalityClauseContainer.cpp.
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
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"

#include "Saturation/LimitClauseContainer.hpp"

namespace Saturation
{

using namespace Shell;


void LimitClauseContainer::add(Clause* c) {
  CALL("LimitClauseContainer::add");
  
  _literalsToClause.insert((*c)[0], c);
}

Clause* LimitClauseContainer::getClause(Literal* l){  
  Clause* res;
  if(_literalsToClause.find(l, res)){
    return res;
  }
  return 0;
}

}
