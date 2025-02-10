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
 * Defines a bi-directional HashMap. This data structure is just a convenient abstraction using two `Map`s under the hood.
 */

#ifndef __LIB__BI_MAP__HPP__
#define __LIB__BI_MAP__HPP__

#include "Lib/Map.hpp"

namespace Lib {

/**
 * A bidirectional hash map, implemented using two @c Map s under the hood. 
 * The methods behave the same as their counterparts in @c Map, with the exception that BiMap
 * asserts that every key, as well as every value is unique in this map (which is necessary to do a bijective mapping.) */
template<class A, class B, class HashA, class HashB>
class BiMap : Map<A,B, HashA>
{
  using Self = Map<A,B,HashA>;
  using Inv = Map<B,A,HashB>;
  Inv _inv;
public:

  BiMap() : Self() {}

  decltype(auto) getInv(B const& val)       { return _inv.get(val); }
  decltype(auto) getInv(B const& val) const { return _inv.get(val); }
  decltype(auto) tryGetInv(B const& val)       { return _inv.tryGet(val); }
  decltype(auto) tryGetInv(B const& val) const { return _inv.tryGet(val); }
  decltype(auto) findInv(B const& val) const { return _inv.find(val); }

  // /** @see Map::get */
  // using Inv::get;

  /** @see Map::get */
  using Self::get;

  // /** @see Map::tryGet */
  // using Inv::tryGet;

  /** @see Map::tryGet */
  using Self::tryGet;

  // /** @see Map::find */
  // using Inv::find;

  /** @see Map::find */
  using Self::find;

  /** @see Map::getOrInit */
  template<class InitFn>
  B& getOrInit(A key, InitFn init) 
  {
    return Self::getOrInit(key, [&]() {
        auto val = init();
        _inv.insert(val, key);
        return val;
    });
  } 

  /** @see Map::clear */
  void clear() 
  {
    _inv.clear();
    Self::clear();
  }

  /** 
   * @see Map::insert 
   * @pre Asserts that both key and value do not yet exist in this BiMap.
   */
  inline void insert(A key, B val)
  {
    ASS(!find(key))
    ASS(!find(val))
    _inv.insert(val, key);
    Self::insert(key, val);
  }


  /** 
   * @see Map::size 
   */
  inline unsigned size() const
  {
    ASS_EQ(_inv.size(), Self::size());
    return _inv.size();
  }

  friend std::ostream& operator<<(std::ostream& out, BiMap const& self) 
  { return out << static_cast<Self const&>(self); }
};


} // namespace Lib

#endif // __LIB__BI_MAP__HPP__
