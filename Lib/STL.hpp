#ifndef STL_HPP
#define STL_HPP

#include <memory>
#include <utility>
#include <vector>
#include "Lib/STLAllocator.hpp"

namespace Lib {

template< typename T >
using vvector = std::vector<T, STLAllocator<T>>;

/** See https://en.cppreference.com/w/cpp/memory/unique_ptr/make_unique
 *
 * Helper function that does not exist in C++11 yet.
 * Replace with std::make_unique once we switch to C++14 or later.
 */
template<typename T, typename... Args>
std::unique_ptr<T> make_unique(Args&&... args)
{
    return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}

}

#endif /* !STL_HPP */