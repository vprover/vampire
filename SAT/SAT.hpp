/**
 * @file SAT/SAT.hpp
 * Defines some global functions for variables, literals and assignments.
 *
 * @since 09/10/2006 Manchester
 */

#ifndef __SAT__
#define __SAT__

namespace SAT {

/**
 * Return the variable corresponding to the literal @b lit
 */
inline
unsigned var (unsigned lit)
{
  return lit >> 1;
} // var

/**
 * Return the positive literal corresponding to the variable @b var
 */
inline
unsigned positiveLiteral (unsigned var)
{
  return var*2;
} // positiveLiteral

/**
 * Return the negative literal corresponding to the variable @b var
 */
inline
unsigned negativeLiteral (unsigned var)
{
  return var*2 + 1;
} // negativeLiteral

/**
 * Return the literal complementary to @b lit
 */
inline
unsigned complementary (unsigned lit)
{
  return lit ^ 1u;
} // complementary

/**
 * Values assigned to variables.
 */
enum Value {
  TRUE = -1,
  FALSE = 1,
  UNASSIGNED = 0
};


}
#endif 
