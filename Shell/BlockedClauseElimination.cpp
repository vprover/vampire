/**
 * @file BlockedClauseElimination.cpp
 * Implements class Blocked Clause Elimination.
 */

#include "BlockedClauseElimination.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

void BlockedClauseElimination::apply(Problem& prb)
{
  CALL("BlockedClauseElimination::apply(Problem&)");

  /*
  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
  */
  prb.invalidateProperty();
}



}
