/**
 * @file ArithmeticKB.cpp
 * Implements class ArithmeticKB.
 */

#include "Kernel/Term.hpp"

#include "ArithmeticKB.hpp"

namespace Kernel
{
namespace Algebra
{

#if 0
/**
 * Return true iff @b t has to be non-equal to @b val.
 * If the fact is a tautology, assign 0 to @b premise, otherwise
 * assign into @b premise the clause that implies it.
 */
bool ArithmeticKB::isNonEqual(TermList t, InterpretedType val, Clause*& premise)
{
  return false;
}

/**
 * Return true iff @b t has to be greater than @b val.
 * If the fact is a tautology, assign 0 to @b premise, otherwise
 * assign into @b premise the clause that implies it.
 */
bool ArithmeticKB::isGreater(TermList t, InterpretedType val, Clause*& premise)
{
  return false;
}

/**
 * Return true iff @b t has to be less than @b val.
 * If the fact is a tautology, assign 0 to @b premise, otherwise
 * assign into @b premise the clause that implies it.
 */
bool ArithmeticKB::isLess(TermList t, InterpretedType val, Clause*& premise)
{
  return false;
}
#endif

}
}
