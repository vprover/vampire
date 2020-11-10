/**
 * Usage:
 *
 *    cdebug() << "message: " << 123;
 *
 * If DEBUG_STREAM_ENABLED is true, prints the message to std:cerr,
 * and automatically adds a newline character at the end.
 *
 * Otherwise, do nothing.
 *
 * By default, DEBUG_STREAM_ENABLED is only enabled in debug mode.
 */

#ifndef DEBUG_STREAM_HPP
#define DEBUG_STREAM_HPP

#include <iostream>
#include <sstream>
#include "Lib/STLAllocator.hpp"


class cls_noendl { };  // TODO: find better name?
#define noendl cls_noendl()


class debug_stream
  : public std::basic_ostringstream<char, std::char_traits<char>, Lib::STLAllocator<char>>
{
  private:
    bool newline = true;

  public:
    ~debug_stream() override
    {
      if (newline) {
        std::cerr << this->str() << std::endl;
      } else {
        std::cerr << this->str();
      }
    }

    debug_stream& operator<<(cls_noendl)
    {
      newline = false;
      return *this;
    }
};


class null_stream
{
  public:
    template <typename T>
    null_stream& operator<<(T&& value)
    {
      // do nothing
      return *this;
    }
};

#endif /* !DEBUG_STREAM_HPP */


// By default, enable output in debug mode
#ifndef DEBUG_STREAM_ENABLED
#   define DEBUG_STREAM_ENABLED VDEBUG
#endif

#ifdef cdebug
#   undef cdebug
#endif

#if DEBUG_STREAM_ENABLED
#   define cdebug debug_stream()
#else
#   define cdebug null_stream()
#endif

#undef DEBUG_STREAM_ENABLED
