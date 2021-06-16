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
using v_map = std::map<Key, T, Compare, STLAllocator<std::pair<const Key, T>>>;


template< typename Key
        , typename Compare = std::less<Key>
        >
using v_set = std::set<Key, Compare, STLAllocator<Key>>;


template< typename Key
        , typename T
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using v_unordered_map = std::unordered_map<Key, T, Hash, KeyEqual, STLAllocator<std::pair<const Key, T>>>;


template< typename Key
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using v_unordered_set = std::unordered_set<Key, Hash, KeyEqual, STLAllocator<Key>>;


template< typename T >
using v_vector = std::vector<T, STLAllocator<T>>;
template< typename T >
using vvector = std::vector<T, STLAllocator<T>>;



}  // namespace Lib

#endif /* !STL_HPP */
