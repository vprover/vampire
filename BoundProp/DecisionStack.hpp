/**
 * @file DecisionStack.hpp
 * Defines class DecisionStack.
 */

#ifndef __DecisionStack__
#define __DecisionStack__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/Stack.hpp"

namespace BoundProp {

using namespace Lib;
using namespace Kernel;

class DecisionStack {
public:
  DecisionLevel depth() const { return _data.size(); }

  void addDecision(Var v) {
    ASS(!_data.find(v));
    _data.push(v);
  }

  void backtrack(DecisionLevel lev) { _data.truncate(lev); }

  Var getDecisionVar(DecisionLevel lev) const { ASS_G(lev,0); return _data[lev-1]; }

  DecisionLevel getVarLevel(Var v) const;

private:
  typedef Stack<Var> VarStack;

  VarStack _data;
};

}
#endif //GNUMP
#endif // __DecisionStack__
