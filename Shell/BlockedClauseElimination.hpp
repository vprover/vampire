/**
 * @file BlockedClauseElimination.hpp
 * Defines class BlockedClauseElimination.
 */


#ifndef __BlockedClauseElimination__
#define __BlockedClauseElimination__

#include "Forwards.hpp"

#include "Kernel/Problem.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class for flattening clauses to separate theory and non-theory parts
 */
class BlockedClauseElimination
{
public:
  void apply(Problem& prb);

private:

};

};

#endif /* __BlockedClauseElimination__ */
