/**
 * @file ConstantRemover.hpp
 * Defines class ConstantRemover.
 */

#ifndef __ConstantRemover__
#define __ConstantRemover__
#if GNUMP

#include "Forwards.hpp"

#include "Lib/DArray.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class ConstantRemover {
public:
  ConstantRemover();

  bool apply(ConstraintRCList*& lst);
private:
  void reset();
  bool scan(ConstraintRCList* lst);

  struct DefiningPair {
    DefiningPair() : left(0), right(0), isTight(false) {}

    ConstraintRCPtr left;
    ConstraintRCPtr right;

    bool isTight;
  };

  Var _varCnt;
  DArray<DefiningPair> _vals;
};

}
#endif //GNUMP
#endif // __ConstantRemover__
