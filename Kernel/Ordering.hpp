/**
 * @file Ordering.hpp
 * Defines (abstract) class Ordering for simplification orderings
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __Ordering__
#define __Ordering__

#include "../Forwards.hpp"

#include "../Lib/Comparison.hpp"
#include "../Lib/SmartPtr.hpp"

namespace Kernel {

/**
 * An abstract class for simplification orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class Ordering
{
public:
  /** Represents the results of ordering comparisons */
  enum Result {
    GREATER,
    LESS,
    GREATER_EQ,
    LESS_EQ,
    EQUAL,
    INCOMPARABLE
  };
  virtual ~Ordering() {}
  /** Return the result of comparing @b l1 and @b l2 */
  virtual Result compare(Literal* l1,Literal* l2) = 0;
  /** Return the result of comparing terms (not term lists!)
   * @b t1 and @b t2 */
  virtual Result compare(TermList t1,TermList t2) = 0;

  virtual Comparison compareFunctors(unsigned fun1, unsigned fun2) = 0;

  void removeNonMaximal(LiteralList*& lits);

  static Result fromComparison(Comparison c);

  static Ordering* instance();
  static bool orderingCreated();
private:
  static OrderingSP s_instance;
}; // class Ordering

}

#endif
