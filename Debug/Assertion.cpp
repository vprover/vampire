/**
 * @file Assertion.cpp
 * Implements assertions.
 */

#include "Assertion.hpp"
#include "Tracer.hpp"

#if VDEBUG

using namespace Debug;

bool Assertion::_violated = false;

/**
 * Called when an assertion is violated. Simply print the stack and
 * throw an assertion violation exception.
 */
void Assertion::violated (const char* file,int line,const char* cond)
{
  if (_violated) {
    return;
  }

  _violated = true;
  cout << "Condition in file " << file << ", line " << line
       << " violated:\n" << cond << "\n"
       << "----- stack dump -----\n";
  Tracer::printStack(cout);
  cout << "----- end of stack dump -----\n";
} // Assertion::violated

/**
 * Called when an exception is thrown as part of the ASSERT_VALID call.
 * Simply print the location and argument of the ASSERT_VALID statement.
 */
void Assertion::reportAssertValidException (const char* file,int line,const char* obj)
{
  cout << "An exception was thrown by the ASSERT_VALID on object " << obj
       << " in file " << file << ", line " << line << ".\n";
} // Assertion::violated

/**
 * Create a new AssertionViolationException.
 */
AssertionViolationException::AssertionViolationException (const char* file,
							  int line)
  : _file(file),
    _line(line)
{
}

/**
 * Write a description of the exception to a stream.
 */
void AssertionViolationException::cry (ostream& str)
{
  str << "Assertion violation ";
  outputFileAndLine(str);
  str << '\n';
} // AssertionViolationException::cry


/**
 * Output (file: file, line: line) to an ostream.
 */
void AssertionViolationException::outputFileAndLine (ostream& str) const
{
  str << "(file: '" << _file
      << "', line: " << _line << ")";
} // AssertionViolationException::outputFileAndLine

#endif // VDEBUG
