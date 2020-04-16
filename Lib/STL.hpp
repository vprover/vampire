#ifndef STL_HPP
#define STL_HPP

#include <algorithm>
#include <map>
#include <memory>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#include "Lib/STLAllocator.hpp"

namespace Lib {


template< typename Key
        , typename T
        , typename Compare = std::less<Key>
        >
using vmap = std::map<Key, T, Compare, STLAllocator<std::pair<const Key, T>>>;


template< typename Key
        , typename Compare = std::less<Key>
        >
using vset = std::set<Key, Compare, STLAllocator<Key>>;


template< typename Key
        , typename T
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using vunordered_map = std::unordered_map<Key, T, Hash, KeyEqual, STLAllocator<std::pair<const Key, T>>>;


template< typename Key
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using vunordered_set = std::unordered_set<Key, Hash, KeyEqual, STLAllocator<Key>>;


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


/** See https://en.cppreference.com/w/cpp/utility/exchange
 *
 * Helper function that does not exist in C++11 yet.
 * Replace with std::exchange once we switch to C++14 or later.
 */
template<class T, class U = T>
T exchange(T& obj, U&& new_value)
{
    T old_value = std::move(obj);
    obj = std::forward<U>(new_value);
    return old_value;
}


}  // namespace Lib

#endif /* !STL_HPP */
