/**
 * @file Assertion.cpp
 * Implements assertions.
 */

#include <string.h>

#include "Assertion.hpp"
#include "Tracer.hpp"

#if VDEBUG

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
#include "../Shell/Options.hpp"

using namespace Lib;
using namespace Debug;

bool Assertion::_violated = false;

void Assertion::printFailureHeader()
{
  if(env.options->mode()==Shell::Options::MODE_SPIDER) {
    env.out << "! " << env.options->problemName();
    env.out << " " << env.timer->elapsedDeciseconds();
    env.out << " " << env.options->testId() << "\n";
  }
}

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
  printFailureHeader();
  cout << "Condition in file " << file << ", line " << line
       << " violated:\n" << cond << "\n"
       << "----- stack dump -----\n";
  Tracer::printStack(cout);
  cout << "----- end of stack dump -----\n";
} // Assertion::violated


void Assertion::violatedStrEquality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const char* val1, const char* val2)
{
  if (_violated) {
    return;
  }

  _violated = true;
  printFailureHeader();
  std::cout << "Condition for string equality "<<val1Str<<" == "<<val2Str
       << " in file " << file << ", line " << line
       << " was violated, as:\n" << val1Str<<" == \""<<val1 <<"\"\n"
       << val2Str<<" == \""<<val2 << "\"\n"
       << "----- stack dump -----\n";
  Tracer::printStack(cout);
  std::cout << "----- end of stack dump -----\n";
}


void Assertion::checkType(const char* file,int line,const void* ptr, const char* assumed,
	const char* ptrStr)
{
  if (_violated) {
    return;
  }

  Allocator::Descriptor* desc = Allocator::Descriptor::find(ptr);

  if(!desc) {
    printFailureHeader();
    cout << "Type condition in file " << file << ", line " << line
         << " violated:\n" << ptrStr << " was not allocated by Lib::Allocator.\n";
  } else if( strcmp(assumed, desc->cls) ) {
    printFailureHeader();
    cout << "Type condition in file " << file << ", line " << line
         << " violated:\n" << ptrStr << " was allocated as \"" << desc->cls
         << "\" instead of \"" << assumed <<"\".\n";
  } else if( !desc->allocated ) {
    printFailureHeader();
    cout << "Type condition in file " << file << ", line " << line
         << " violated:\n" << ptrStr << " was allocated as \"" << desc->cls
         << "\", but no longer is.\n";
  } else {
    return;
  }

  _violated = true;
  cout << "----- stack dump -----\n";
  Tracer::printStack(cout);
  cout << "----- end of stack dump -----\n";
  throw Debug::AssertionViolationException(file,line);
} // Assertion::violated

/**
 * Called when an exception is thrown as part of the ASSERT_VALID call.
 * Simply print the location and argument of the ASSERT_VALID statement.
 */
void Assertion::reportAssertValidException (const char* file,int line,const char* obj)
{
  cout << "An exception was thrown by ASSERT_VALID on object " << obj
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
