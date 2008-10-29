/**
 * @file SAT/Assignment.hpp
 * Defines class Assignment for assignment to variables.
 *
 * @since 09/10/2006 Manchester
 */

#ifndef __SATAssignment__
#define __SATAssignment__

#include "../Debug/Assertion.hpp"

#include "../SAT/SAT.hpp"

namespace SAT {

/**
 * Class Assignment for assignment to variables.
 */
class Assignment
{
public:
  explicit Assignment(unsigned lastVar);
  ~Assignment();
  /** Get the value of variable @b var */
  inline Value get(unsigned var)
  {
    ASS(var <= _lastVar);
    return _values[var];
  } // Assignment::get

  /** Set the value of variable @b var to @b val */
  inline Value set(unsigned var,Value val)
  {
    ASS(var <= _lastVar);
    _values[var] = val;
  } // Assignment::set

  void stretchToFit(unsigned var);
private:
  /** last variable number */
  unsigned _lastVar;
  /** size */
  unsigned _size;
  /** array of values */
  Value* _values;
}; // class Assignment


}
#endif 
