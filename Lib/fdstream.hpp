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
 * @file fdstream.hpp
 * Defines class fdstream.
 */

#ifndef __fdstream__
#define __fdstream__

#include "Portability.hpp"

#include <unistd.h>
#include <cerrno>
#include <iostream>
#include <streambuf>

#include "Forwards.hpp"

#include "Exception.hpp"

namespace Lib {

template <
  typename CharType,
  typename CharTraits = std::char_traits <CharType>
  >
class basic_fdbuf: public std::basic_streambuf <CharType, CharTraits>
{
public:
  typedef CharType                                char_type;
  typedef CharTraits                              traits_type;
  typedef typename traits_type::int_type          int_type;
  typedef typename traits_type::pos_type          pos_type;
  typedef typename traits_type::off_type          off_type;

  typedef basic_fdbuf <char_type, traits_type> this_type;

  basic_fdbuf( int fd ) : _fd( fd ), _preRead(-1)
  { }

  ~basic_fdbuf()
  {
  }

  int_type getPreReadChar() const { return _preRead; }
  void setPreReadChar(int_type val) { _preRead=val; }
protected:
//  /**
//   * Get the CURRENT character without advancing the file pointer
//   */
  virtual int_type underflow()
  {
    if(_preRead!=-1) {
      return _preRead;
    }
    int_type ch=uflow();
    if(ch!=traits_type::eof()) {
      _preRead=ch;
    }
    return ch;
  }

  virtual streamsize xsgetn ( char_type * s0, streamsize n0 )
  {
    char_type * s=s0;
    streamsize n=n0;
    if(_preRead!=-1) {
      *(s++)=_preRead;
      n--;
      _preRead=-1;
    }
    if(n==0) {
      return n0-n;
    }
    errno=0;
    ssize_t res=read(_fd, s, n*sizeof(char_type));
    if(res<0) {
      SYSTEM_FAIL("read in xsgetn", errno);
      return n0-n;
    }
    return (n0-n)+res/sizeof(char_type);
  }

  /**
   * Get the CURRENT character AND advance the file pointer
   */
  virtual int_type uflow()
  {
    if(_preRead!=-1) {
      int_type res=_preRead;
      _preRead=-1;
      return res;
    }

    char_type ch;
    errno=0;
    ssize_t res=read(_fd, &ch, sizeof(char_type));
    if(res<0) {
      SYSTEM_FAIL("read in uflow", errno);
      return traits_type::eof();
    }

    return (res==sizeof(char_type)) ? ch : traits_type::eof();
  }

  virtual int_type sync()
  {
    _preRead=-1; //we throw away the preread char
    return 0;
  }

  virtual streamsize xsputn (const char_type * s, streamsize n)
  {
    ssize_t res=write(_fd, s, n*sizeof(char_type));
    if(res<0) {
      return 0;
    }
    return res/sizeof(char_type);
  }

  virtual int_type overflow( int_type c = traits_type::eof() )
  {
    char_type ch=c;
    ssize_t res=write(_fd, &ch, sizeof(char_type));
    return (res==sizeof(char_type)) ? 0 : traits_type::eof();
  }

private:
  int _fd;
  int_type _preRead;
};


template <
typename CharType,
typename CharTraits = std::char_traits <CharType>
>
struct basic_fdstream: public std::basic_iostream <CharType, CharTraits>
{
  typedef CharType                                      char_type;
  typedef CharTraits                                    traits_type;

  typedef basic_fdbuf      <char_type, traits_type>  sbuf_type;
  typedef basic_fdstream   <char_type, traits_type>  this_type;
  typedef std::basic_iostream <char_type, traits_type>  base_type;

  basic_fdstream( int fd ):
    base_type( new sbuf_type( fd ) )
  { }

  ~basic_fdstream()
  { delete static_cast<sbuf_type*>(this->rdbuf()); }

  typename traits_type::int_type getPreReadChar() const
  { return static_cast<sbuf_type*>(this->rdbuf())->getPreReadChar(); }
  void setPreReadChar(typename traits_type::int_type val)
  { return static_cast<sbuf_type*>(this->rdbuf())->setPreReadChar(val); }
};

typedef basic_fdbuf    <char> fdbuf;
typedef basic_fdstream <char> fdstream;

}

#endif // __fdstream__
