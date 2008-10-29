/**
 * @file Ordering.hpp
 * Defines (abstract) class Ordering for simplification orderings
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __Ordering__

namespace Kernel {

class Literal;
class TermList;

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
  /** Return the result of comparing @b l1 and @b l2 */
  virtual Result compare(const Literal* l1,const Literal* l2) = 0;
  /** Return the result of comparing terms (not term lists!)
   * @b t1 and @b t2 */
  virtual Result compare(const TermList* t1,const TermList* t2) = 0;
}; // class Ordering

}
#endif 
