
/*
 * File ConstantRemover.hpp.
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
