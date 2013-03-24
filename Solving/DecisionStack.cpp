/**
 * @file DecisionStack.cpp
 * Implements class DecisionStack.
 */
#if GNUMP
#include "DecisionStack.hpp"

namespace Solving
{

/**
 * Return the level on which variable @c v is a decision point, or
 * -1 if it is not a decision point.
 */
DecisionLevel DecisionStack::getVarLevel(Var v) const
{
  CALL("DecisionStack::getVarLevel");

  DecisionLevel sz = _data.size();
  for(DecisionLevel i=0; i<sz; i++) {
    if(_data[i]==v) {
      return i+1;
    }
  }
  return -1;
}

}
#endif //GNUMP
