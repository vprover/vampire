
/*
 * File ExtensionalityClauseContainer.hpp.
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
#ifndef __LimitClauseContainer__
#define __LimitClauseContainer__

#include "Forwards.hpp"

#include "Kernel/Sorts.hpp"

#include "Shell/Options.hpp"

#include "Lib/Environment.hpp"

namespace Saturation
{

using namespace Kernel;
using namespace Shell;


/**
 * Container for tracking extensionality-like clauses, i.e. clauses with exactly
 * one positive equality between variables.
 */
class LimitClauseContainer
{
public:
  CLASS_NAME(LimitClauseContainer);
  USE_ALLOCATOR(LimitClauseContainer);

  LimitClauseContainer()
  {}

  void add(Clause* c);
  Clause* getClause(Literal* lit);
private:

  DHMap<Literal*, Clause*> _literalsToClause;
};

}

#endif /*__LimitClauseContainer__*/
