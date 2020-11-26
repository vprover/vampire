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
 * @file VString.hpp
 * Vampire string is basic_string equipped with STLAllocator,
 * so that it's allocated via vampire's Allocator.
 * 
 * @since 5/8/2014 Prague.
 * @author Martin Suda
 */


#ifndef __VString__
#define __VString__

#include <string>
#include <sstream>

#include "STLAllocator.hpp"

namespace Lib {
  
// ostringstream which uses (returns) a vstring
typedef std::basic_ostringstream<char,std::char_traits<char>,STLAllocator<char> > vostringstream_base;

struct vostringstream : public vostringstream_base {
  CLASS_NAME(vostringstream);
  USE_ALLOCATOR(vostringstream);
  
  // inherit parent's constructors (c++11)
  using vostringstream_base::vostringstream_base;
};

// istringstream which uses (returns) a vstring
typedef std::basic_istringstream<char,std::char_traits<char>,STLAllocator<char> > vistringstream_base;

struct vistringstream : public vistringstream_base {
  CLASS_NAME(vistringstream);
  USE_ALLOCATOR(vistringstream);
  
  // inherit parent's constructors (c++11)
  using vistringstream_base::vistringstream_base;
};

// stringstream which uses (returns) a vstring 
typedef std::basic_stringstream<char,std::char_traits<char>,STLAllocator<char> > vstringstream_base;

struct vstringstream : public vstringstream_base {
  CLASS_NAME(vstringstream);
  USE_ALLOCATOR(vstringstream);
  
  // inherit parent's constructors (c++11)
  using vstringstream_base::vstringstream_base;
};

// vampire string, a STL string using vampire's Allocator
typedef std::basic_string<char,std::char_traits<char>,STLAllocator<char> > vstring;

/* 
 * Careful: doing the above inheritance trick with vstring might not be a good idea.
 * For one, basic_string does not have a virtual destructor so inheriting
 * from it is not a nice thing (although slicing problems shouldn't occur
 * if we just add the operator new functions and no data members ... )
 * For the other, it's not that simple to make it work anyway. For instance,
 * the globally available operators + for strings, would take vstring as argument
 * but still return only the parent, vstring_base. One would need to
 * redefine all of them and make an ugly explicit downcast.
 */

} // namespace Lib

#endif // __VString__
