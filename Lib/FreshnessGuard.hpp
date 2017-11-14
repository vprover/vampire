
/*
 * File FreshnessGuard.hpp.
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
 * @file FreshnessGuard.hpp
 * Defines class FreshnessGuard.
 */

#ifndef __FreshnessGuard__
#define __FreshnessGuard__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Exception.hpp"

namespace Lib {

/**
 * Some objects can be used only once. This auxiliary object
 * can be used to enforce this constraint.
 */
class FreshnessGuard {
public:
  FreshnessGuard() : _fresh(true) {}

  bool isFresh() const { return _fresh; }
  /**
   * This function can be called only when the object is fresh.
   * It makes the object non-fresh.
   */
  void use() {
    CALL("FreshnessGuard::use");
    ASS(isFresh());
    if(!isFresh()) {
      INVALID_OPERATION("using non-fresh object");
    }
    _fresh = false;
  }

  void refresh() {
    _fresh = true;
  }

private:
  bool _fresh;
};

}

#endif // __FreshnessGuard__
