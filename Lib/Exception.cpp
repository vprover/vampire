/**
 * Class Exception.cpp. Implements Vampire exceptions.
 *
 * @since 03/12/2003, Manchester 
 */

#include "Exception.hpp"

using namespace Lib;

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
} // UserErrorException::cry





