/**
 * @file Comparison.hpp
 * Defines the Compare enum
 * @since 25/12/2003 Manchester
 */

#ifndef __VL_COMPARE__
#define __VL_COMPARE__


namespace Lib {

/**
 * Type denoting the result of comparison.
 */
enum Comparison
{
  LESS = -1,
  EQUAL = 0,
  GREATER = 1
};

/**
 * Type denoting the result of comparison of simplification orderings.
 * @since 25/03/2007 Manchester
 */
enum PartialComparison
{
  PC_LESS = -1,
  PC_EQUAL = 0,
  PC_GREATER = 1,
  PC_INCOMPARABLE = 2
};

}

#endif
