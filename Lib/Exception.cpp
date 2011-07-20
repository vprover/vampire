/**
 * Class Exception.cpp. Implements Vampire exceptions.
 *
 * @since 03/12/2003, Manchester
 */

#include <string.h>

#include "Int.hpp"

#include "Exception.hpp"

namespace Lib
{

int Exception::s_exceptionCounter=0;

Exception::Exception (const char* msg, int line)
  : _message((string(msg)+": "+Int::toString(line)).c_str())
{ s_exceptionCounter++; }

/**
 * Write a description of the exception to a stream.
 */
void Exception::cry (ostream& str)
{
  str << _message << "\n";
} // Exception::cry


/**
 * Write a description of the exception to a stream.
 */
void UserErrorException::cry (ostream& str)
{
  str << "User error: " << _message << "\n";
} // UserErrorException::cry

/**
 * Write a description of the exception to a stream.
 */
void InvalidOperationException::cry (ostream& str)
{
  str << "Invalid operation: " << _message << "\n";
} // InvalidOperationException::cry


SystemFailException::SystemFailException(const string msg, int err)
: Exception(msg+" error "+Int::toString(err)+": "+strerror(err)), err(err)
{}
/**
 * Write a description of the exception to a stream.
 */
void SystemFailException::cry (ostream& str)
{
  str << "System fail: " << _message << "\n";
} // SystemFailException::cry


/**
 * Write a description of the exception to a stream.
 */
void NotImplementedException::cry (ostream& str)
{
  str << "Not implemented at " << file << ":" << line << "\n";
} // NotImplementedException::cry


}
