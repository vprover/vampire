/**
 * @file EqualityVariableRemover.hpp
 * Defines class EqualityVariableRemover.
 */

#ifndef __EqualityVariableRemover__
#define __EqualityVariableRemover__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/Set.hpp"

#include "Kernel/V2CIndex.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class EqualityVariableRemover {
public:
  EqualityVariableRemover() { reset(); }

  bool apply(ConstraintRCList*& lst);
private:
  void reset();
  void scan(ConstraintRCList* lst);

  Var getEliminatedVariable(Constraint& c);

  void eliminate(Constraint* c, ConstraintRCList*& lst);

  bool allowedEquality(Constraint& c);

  struct ConstraintHash
  {
    static unsigned hash(const Constraint* c);
    static bool equals(const Constraint* c1, const Constraint* c2);
  };

  Set<Constraint*,ConstraintHash> _halves;
  DHMap<Constraint*, Constraint*> _equalities;
  V2CIndex _v2c;
};

}
#endif //GNUMP
#endif // __EqualityVariableRemover__
