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
 * Class Exception.hpp. Defines Vampire exceptions.
 *
 * @since 03/12/2003, Manchester
 */

#ifndef __Exception__
#define __Exception__

#include <iostream>
#include <sstream>
#include <string>

namespace Lib {


/**
 * Base for every class that is to be thrown
 */
class ThrowableBase
{
};

template<class... Ms>
struct OutputAll;

template<class M, class... Ms>
struct OutputAll<M,Ms...> {
  static void apply(std::ostream& out, M m, Ms... ms) {
    out << m;
    OutputAll<Ms...>::apply(out, ms...);
  }
};

template<>
struct OutputAll<> {
  static void apply(std::ostream& out) { }
};

/**
 * Abstract class Exception. It is the base class for
 * several concrete classes.
 */
class Exception : public ThrowableBase
{
  template<class... Msg>
  std::string toString(Msg... msg){
    std::stringstream out;
    OutputAll<Msg...>::apply(out, msg...);
    return out.str();
  }
public:
  /** Create an exception with a given error message */
  explicit Exception (const char* msg) : _message(msg) {}
  Exception (const char* msg, int line);
  explicit Exception (const std::string msg) : _message(msg) {}

  template<class... Msg>
  explicit Exception(Msg... msg)
   : Exception(toString(msg...))
  { }

  virtual void cry (std::ostream&) const;
  virtual ~Exception() {}

  const std::string& msg() { return _message; }
protected:
  /** Default constructor, required for some subclasses, made protected
   * so that it cannot be called directly */
  Exception () {}
  /** The error message */
  std::string _message;

  friend std::ostream& operator<<(std::ostream& out, Exception const& self)
  { self.cry(out); return out; }

}; // Exception

class ParsingRelatedException : public Exception { using Exception::Exception; };

/**
 * Class UserErrorException. A UserErrorException is thrown
 * when a user error occurred, for example, a file name is
 * specified incorrectly; an invalid option to Vampire
 * was given, or there is a syntax error in the input file.
 */
class UserErrorException
  : public ParsingRelatedException
{
 public:
  using ParsingRelatedException::ParsingRelatedException;

  // input line related to the error: non-zero if set
  unsigned line = 0;
  std::string filename;
  void cry (std::ostream&) const override;
}; // UserErrorException

/**
 * Class ValueNotFoundException. A ValueNotFoundException is
 * thrown when a value is not found in some collection.
 * Currently it is being thrown by the NameArray objects.
 */
class ValueNotFoundException
  : public Exception
{
 public:
   ValueNotFoundException ()
    : Exception("")
  {}
}; // UserErrorException

/**
 * Class TimeLimitExceededException.
 */
class TimeLimitExceededException
: public Exception
{
public:
  TimeLimitExceededException ()
  : Exception("The time limit exceeded")
  {}
}; // TimeLimitExceededException

/**
 * Class ActivationLimitExceededException.
 */
class ActivationLimitExceededException
: public Exception
{
public:
  ActivationLimitExceededException ()
  : Exception("The activation limit exceeded")
  {}
}; // ActivationLimitExceededException


/**
 * Class InvalidOperationException.
 */
class InvalidOperationException
  : public Exception
{
 public:
   InvalidOperationException (const char* msg)
    : Exception(msg)
  {}
   InvalidOperationException (const std::string msg)
    : Exception(msg)
  {}
  void cry (std::ostream&) const override;
}; // InvalidOperationException

/**
 * Class SystemFailException.
 */
class SystemFailException
  : public Exception
{
public:
  SystemFailException (const std::string msg, int err);
  void cry (std::ostream&) const override;

  int err;
}; // InvalidOperationException

/**
 * Class NotImplementedException.
 */
class NotImplementedException
  : public Exception
{
 public:
   NotImplementedException (const char* file,int line)
    : Exception(""), file(file), line(line)
  {}
   void cry (std::ostream&) const override;
 private:
   const char* file;
   int line;
}; // InvalidOperationException


}

#define VAMPIRE_EXCEPTION \
  throw Lib::Exception(__FILE__,__LINE__)
#define USER_ERROR(...) \
  throw Lib::UserErrorException(__VA_ARGS__)
#define INVALID_OPERATION(msg) \
  throw Lib::InvalidOperationException(msg)
#define SYSTEM_FAIL(msg,err) \
  throw Lib::SystemFailException(msg,err)
#define NOT_IMPLEMENTED \
  throw Lib::NotImplementedException(__FILE__, __LINE__)

#endif // __Exception__



