/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Assertion.cpp
 * Implements assertions.
 */

#if VDEBUG
#include <cstring>
#include <ostream>

#include "Assertion.hpp"
#include "Tracer.hpp"
#include "Lib/System.hpp"

using namespace Lib;
using namespace Shell;
using namespace Debug;

namespace Shell {
void reportSpiderFail();
}

[[noreturn]] void Assertion::abortAfterViolation()
{
  Shell::reportSpiderFail();
  System::terminateImmediately(VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION);
}

/**
 * Called when an assertion is violated. Simply print the stack and
 * throw an assertion violation exception.
 */
void Assertion::violated(Location loc, const char* cond)
{
  if (outputAllowed(true)) {
    std::cout << "Condition at location " << loc
         << " violated:\n"
         << cond << "\n"
         << "----- stack dump -----\n";
    Tracer::printStack();
    std::cout << "----- end of stack dump -----" << std::endl;
  }
  abortAfterViolation();
} // Assertion::violated

void Assertion::violatedStrEquality(Location loc, const char* val1Str,
                                    const char* val2Str, const char* val1, const char* val2)
{
  if (outputAllowed(true)) {
    std::cout << "Condition for string equality " << val1Str << " == " << val2Str
              << " at location " << loc
              << " was violated, as:\n"
              << val1Str << " == \"" << val1 << "\"\n"
              << val2Str << " == \"" << val2 << "\"\n"
              << "----- stack dump -----\n";
    Tracer::printStack();
    std::cout << "----- end of stack dump -----\n";
  }
  abortAfterViolation();
}

/**
 * Called when an exception is thrown as part of the ASSERT_VALID call.
 * Simply print the location and argument of the ASSERT_VALID statement.
 */
void Assertion::reportAssertValidException(Location loc, const char* obj)
{
  if (outputAllowed(true)) {
    std::cout << "An exception was thrown by ASSERT_VALID on object " << obj
         << " at location " << loc << ".\n";
  }
  abortAfterViolation();
} // Assertion::violated

#endif // VDEBUG
