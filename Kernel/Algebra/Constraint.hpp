/**
 * @file Constraint.hpp
 * Defines class Constraint.
 */

#ifndef __Constraint__
#define __Constraint__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"

#include "Polynomial.hpp"

namespace Kernel {
namespace Algebra {

using namespace Lib;

/**
 * Object that represents an equality, non-equality or inequality constraint
 *
 * Constraints are stored in the form
 *
 * (Polynomial) # 0, where # is in {=, !=, >, >=}
 */
class Constraint {

  static bool isConstraint(Literal* l);

  Constraint(Literal* lit, bool negate=false);

  CLASS_NAME("Constraint");
  USE_ALLOCATOR(Constraint);

  bool simplify();


  /** Return true iff the constraint is an inequality */
  bool inequality() const  {return _inequality; }

  /** Return true iff the constraint is an non-equality (!=) */
  bool nonEquality() const  {return _negative && !_inequality; }

  /** Return true iff the constraint is a strict inequality (>) */
  bool strictInequality() const  {return !_negative && _inequality; }

  /** Return true iff the constraint is an integer inequality (either > or >=) */
  bool integerInequality() const  { ASS(!_integer || _inequality); return _integer; }

  /** Return true iff the constraint was simplified, compared to what was contained
   * in the literal passed to the constructor */
  bool simplified() const { return _simplified; }

private:

  bool doSimplifications();

  bool _inequality;
  bool _negative;
  bool _integer;

  bool _simplified;

  Polynomial _pol;
};

}
}

#endif // __Constraint__
