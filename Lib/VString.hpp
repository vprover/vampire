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

namespace Lib {
typedef std::string vstring;
typedef std::stringstream vstringstream;
typedef std::istringstream vistringstream;
typedef std::ostringstream vostringstream;
}

#endif // __VString__
