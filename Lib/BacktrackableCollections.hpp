/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Stack.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Backtrackable.hpp"

namespace Lib {

  template<class C>
  struct BdStack : public Stack<C> {
    using Stack<C>::Stack;

    C swapRemove(unsigned idx, BacktrackData& bd)
    {
      auto removed = Stack<C>::swapRemove(idx);
      bd.addClosure([this,removed,idx]() mutable {
          Stack<C>::push(std::move(removed));
          std::swap((*this)[idx], this->top());
      });
      return removed;
    }


    void push(C val, BacktrackData& bd)
    {
      Stack<C>::push(std::move(val));
      bd.addClosure([this] { this->pop(); });
    }
  };

  template<class K, class V>
  struct BdDHMap : public DHMap<K, V> {
    using Super = DHMap<K,V>;
    using DHMap<K,V>::DHMap;

    using Super::remove;

    Option<std::pair<K, V>> remove(K const& key, BacktrackData& bd)
    {
      auto removed = Super::remove(key);
      bd.addClosure([this,removed]() mutable {
          if (removed) {
            Super::insert(std::move(removed->first), std::move(removed->second));
          }
      });
      return removed;
    }


    V replace(K const& key, V val, BacktrackData& bd)
    {
      auto old = Super::find(key);
      ASS(old);
      std::swap(val, *old);
      bd.addClosure([this,key,val]() mutable {
          std::swap(*Super::find(key), val);
      });
      return val;
    }



  };
} // namespace Lib
