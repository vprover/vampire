
/*
 * File HalfBoundingRemover.hpp.
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
 * @file HalfBoundingRemover.hpp
 * Defines class HalfBoundingRemover.
 */

#ifndef __HalfBoundingRemover__
#define __HalfBoundingRemover__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/MapToLIFO.hpp"

#include "Kernel/V2CIndex.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

/**
 * Preprocessing rule that performs half-bounding, almost-half bounding and
 * FM variable elimination according to the options specified in
 * @c env.options.
 */
class HalfBoundingRemover {
public:
  HalfBoundingRemover() { reset(); }

  bool apply(ConstraintRCList*& lst);
private:
  void reset();

  bool applyHalfBoundingRemoval(ConstraintRCList*& lst);
  bool applyAlmostHalfBoundingRemoval(ConstraintRCList*& lst, bool boundsOnly);
  bool applyFMElimination(ConstraintRCList*& lst);

  void doFMReduction(Var v, ConstraintRCList*& constraints);
  void scan(ConstraintRCList* lst);

  V2CIndex _v2c;
};

}
#endif //GNUMP
#endif // __HalfBoundingRemover__
