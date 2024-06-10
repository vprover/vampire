/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef STL_HPP
#define STL_HPP

#include <algorithm>
#include <map>
#include <memory>
#include <set>
#include <type_traits>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace Lib {


template< typename Key
        , typename T
        , typename Compare = std::less<Key>
        >
using vmap = std::map<Key, T, Compare>;


template< typename Key
        , typename Compare = std::less<Key>
        >
using vset = std::set<Key, Compare>;


template< typename Key
        , typename T
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using vunordered_map = std::unordered_map<Key, T, Hash, KeyEqual>;


template< typename Key
        , typename Hash = std::hash<Key>
        , typename KeyEqual = std::equal_to<Key>
        >
using vunordered_set = std::unordered_set<Key, Hash, KeyEqual>;


template< typename T >
using vvector = std::vector<T>;

}  // namespace Lib

#endif /* !STL_HPP */
