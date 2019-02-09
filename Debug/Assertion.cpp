
/*
 * File Assertion.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Assertion.cpp
 * Implements assertions.
 */

#include <string.h>

#include "Assertion.hpp"
#include "Tracer.hpp"

#if VDEBUG

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Shell/Options.hpp"

using namespace Lib;
using namespace Shell;
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
  reportSpiderFail();
  if(outputAllowed(true)) {
    cout << "Condition in file " << file << ", line " << line
	<< " violated:\n" << cond << "\n"
	<< "----- stack dump -----\n";
    Tracer::printStack(cout);
    cout << "----- end of stack dump -----" << endl;
  }
} // Assertion::violated


void Assertion::violatedStrEquality(const char* file,int line,const char* val1Str,
	  const char* val2Str, const char* val1, const char* val2)
{
  if (_violated) {
    return;
  }

  _violated = true;
  reportSpiderFail();
  if(outputAllowed(true)) {
    std::cout << "Condition for string equality "<<val1Str<<" == "<<val2Str
	<< " in file " << file << ", line " << line
	<< " was violated, as:\n" << val1Str<<" == \""<<val1 <<"\"\n"
	<< val2Str<<" == \""<<val2 << "\"\n"
	<< "----- stack dump -----\n";
    Tracer::printStack(cout);
    std::cout << "----- end of stack dump -----\n";
  }
}


void Assertion::checkType(const char* file,int line,const void* ptr, const char* assumed,
	const char* ptrStr)
{
  if (_violated) {
    return;
  }

  VAllocator::Descriptor* desc = VAllocator::Descriptor::find(ptr);

  if(!desc) {
    reportSpiderFail();
    if(outputAllowed(true)) {
      cout << "Type condition in file " << file << ", line " << line
	  << " violated:\n" << ptrStr << " was not allocated by Lib::Allocator.\n";
    }
  } else if( !USE_PRECISE_CLASS_NAMES && strcmp(assumed, desc->cls) ) {
    //TODO: the use of precise class names disrupts the check, fix it in the future!
    reportSpiderFail();
    if(outputAllowed(true)) {
      cout << "Type condition in file " << file << ", line " << line
	   << " violated:\n" << ptrStr << " was allocated as \"" << desc->cls
	   << "\" instead of \"" << assumed <<"\".\n";
    }
  } else if( !desc->allocated ) {
    reportSpiderFail();
    if(outputAllowed(true)) {
      cout << "Type condition in file " << file << ", line " << line
	   << " violated:\n" << ptrStr << " was allocated as \"" << desc->cls
	   << "\", but no longer is.\n";
    }
  } else {
    return;
  }

  _violated = true;

  if(outputAllowed(true)) {
    cout << "----- stack dump -----\n";
    Tracer::printStack(cout);
    cout << "----- end of stack dump -----\n";
  }
  throw Debug::AssertionViolationException(file,line);
} // Assertion::violated

/**
 * Called when an exception is thrown as part of the ASSERT_VALID call.
 * Simply print the location and argument of the ASSERT_VALID statement.
 */
void Assertion::reportAssertValidException (const char* file,int line,const char* obj)
{
  if(outputAllowed(true)) {
    cout << "An exception was thrown by ASSERT_VALID on object " << obj
	<< " in file " << file << ", line " << line << ".\n";
  }
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
