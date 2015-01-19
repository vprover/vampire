/**
 * @file LookAheadVariableSelector.hpp
 * Defines class LookAheadVariableSelector.
 */

#ifndef __LookAheadVariableSelector__
#define __LookAheadVariableSelector__

#if GNUMP

#include "Forwards.hpp"

#include "VariableSelector.hpp"

namespace BoundProp {

using namespace Kernel;

class LookAheadVariableSelector : public VariableSelector {
  friend class VariableSelector;

  struct AheadData;

  LookAheadVariableSelector(Solver& solver);
public:

  virtual Var getNextVariable();

private:

  bool secondIsBetter(AheadData& f, AheadData& s);

  void updateAhead(Var var, Constraint& c, AheadData& d);
  void populateAhead(Var var, AheadData& d);
};

}
#endif //GNUMP
#endif // __LookAheadVariableSelector__
