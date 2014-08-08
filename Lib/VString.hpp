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

// vampire string, a STL string using vampire's Allocator
typedef std::basic_string<char,std::char_traits<char>,STLAllocator<char> > vstring;

// stringstream which uses (returns) a vstring
typedef std::basic_stringstream<char,std::char_traits<char>,STLAllocator<char> > vstringstream;


} // namespace Lib

#endif // __VString__
