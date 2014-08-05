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
#include "Lib/STLAllocator.hpp"

namespace Lib {

// vampire string, a STL string using vampire's Allocator
typedef std::basic_string<char,std::char_traits<char>,STLAllocator<char> >  vstring;

} // namespace Lib

#endif // __VString__
