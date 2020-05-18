
/*
 * File STLAllocator.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file STLAllocator.hpp
 * Allocator class to be passed as a template argument to STL classes 
 * to make use vampire's Allocator instead of the default one.
 * (see http://www.codeproject.com/Articles/4795/C-Standard-Allocator-An-Introduction-and-Implement)
 * 
 * @since 1/8/2014 Prague.
 * @author Martin Suda
 */


#ifndef __STLAllocator__
#define __STLAllocator__

#include <limits>

#include "Lib/Allocator.hpp"

namespace Lib {

template<typename T>
class STLAllocator {
public : 
    //    typedefs
    typedef T value_type;
    typedef value_type* pointer;
    typedef const value_type* const_pointer;
    typedef value_type& reference;
    typedef const value_type& const_reference;
    typedef std::size_t size_type;
    typedef std::ptrdiff_t difference_type;

public : 
    //    convert an allocator<T> to allocator<U>
    template<typename U>
    struct rebind {
        typedef STLAllocator<U> other;
    };

public : 
    inline explicit STLAllocator() {}
    inline ~STLAllocator() {}
    inline explicit STLAllocator(STLAllocator const&) {}
    template<typename U>
    inline STLAllocator(STLAllocator<U> const&) {}

    //    address
    inline pointer address(reference r) { return &r; }
    inline const_pointer address(const_reference r) { return &r; }

    //    memory allocation
    inline pointer allocate(size_type cnt, 
       typename std::allocator<void>::const_pointer = 0) { 
      return reinterpret_cast<pointer>(ALLOC_UNKNOWN(cnt*sizeof(T),"STLAllocator<T>"));           
    }
    inline void deallocate(pointer p, size_type) { 
        DEALLOC_UNKNOWN(p,"STLAllocator<T>");
    }

    //    size
    inline size_type max_size() const { 
        return std::numeric_limits<size_type>::max() / sizeof(T);
 }

    //    construction/destruction
    inline void construct(pointer p, T&& t) { new(p) T(std::move(t)); }
    inline void construct(pointer p, const T& t) { new(p) T(t); }
    inline void destroy(pointer p) { p->~T(); }

    inline bool operator==(STLAllocator const&) const { return true; }
    inline bool operator!=(STLAllocator const& a) const { return !operator==(a); }
};    //    end of class STLAllocator 

extern const STLAllocator<void> global_stl_allocator;

} // namespace Lib

#endif // __STLAllocator__
