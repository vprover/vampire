/**
 * @file SAT/Assignment.cpp
 * Defines class Assignment for assignment to variables.
 *
 * @since 09/10/2006 Manchester
 */

#include "../Debug/Tracer.hpp"

#include "Assignment.hpp"

using namespace SAT;

/**
 * Create an assignment.
 * Initially, all variables are unassigned.
 * @param lastVar a variable, the assignment will be large enough to
 *        accommodate this variable
 * @since 09/10/2006 Manchester
 */
Assignment::Assignment(unsigned lastVar)
  : _lastVar(lastVar),
    _size(lastVar+1),
    _values(new Value[_lastVar+1])
{
  CALL("Assignment::Assignment");

  for (unsigned i = lastVar; i > 0;i--) {
    _values[i] = UNASSIGNED;
  }
} // Assignment::Assignment


/**
 * Destroy the assignment.
 * @since 10/10/2006 Manchester
 */
Assignment::~Assignment()
{
  CALL("Assignment::~Assignment");

  delete [] _values;
} // Assignment::~Assignment

/**
 * Stretch (if needed) so that variable var becomes accessible.
 * Assign UNASSIGNED to all new variables.
 * @since 09/10/2006 Manchester
 */
void Assignment::stretchToFit(unsigned var)
{
  CALL("Assignment::stretchToFit");

  if (var <= _lastVar) {
    return;
  }

  if (var >= _size) { // insufficient size
    unsigned newSize = _size*2;
    if (var >= newSize) {
      newSize = var+1;
    }
    Value* newValues = new Value[newSize];
    for (unsigned i = _lastVar;i > 0;i--) {
      newValues[i] = _values[i];
    }
    delete[] _values;
    _values = newValues;
    _size = newSize;
  }

  for (unsigned i = _lastVar+1;i <= var;i++) {
    _values[i] = UNASSIGNED;
  }
  _lastVar = var;
} // Assignment::stretchToFit
