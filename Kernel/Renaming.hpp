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
 * @file Renaming.hpp
 * Defines class Renaming
 *
 */

#ifndef __Renaming__
#define __Renaming__

#if VDEBUG
#include "Lib/VString.hpp"
#endif

#include "Lib/DHMap.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/TypedTermList.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class Renaming {
public:
  CLASS_NAME(Renaming);
  USE_ALLOCATOR(Renaming);

  Renaming() :
    _nextVar(0), _identity(true), _bank(DEFAULT_BANK) {
  }

  /*
   * Construct a renaming with names starting at firstVar
   */
  Renaming(unsigned firstVar) :
    _nextVar(firstVar), _identity(true), _bank(DEFAULT_BANK) {
  }

  Renaming(unsigned firstVar, VarBank bank) :
    _nextVar(firstVar), _identity(true), _bank(bank) {
  }

  void reset()
  {
    _data.reset();
    _nextVar = 0;
    _identity = true;
    _bank = DEFAULT_BANK;
  }
  bool keepRecycled() const { return _data.keepRecycled() > 0; }

  void init(unsigned firstVar, VarBank bank){
    _data.reset();
    _nextVar = firstVar;
    _identity = true;
    _bank = bank;    
  }

  unsigned getOrBind(unsigned v, VarBank b)
  {
    unsigned res;
    if (_data.findOrInsert(v, res, _nextVar)) {
      _nextVar++;
      if(v!=res || b != _bank) {
        _identity = false;
      }
    }
    return res;
  }
  unsigned get(unsigned v) const
  { return _data.get(v); }
  bool contains(unsigned v)
  { return _data.find(v); }

  VarBank bank() { return _bank; }

  Literal* apply(Literal* l);
  Term* apply(Term* l);
  TermList apply(TermList l);
  bool identity() const;

  void normalizeVariables(const Term* t);
  void normalizeVariables(TermList t);
  void makeInverse(const Renaming& orig);

  static Literal* normalize(Literal* l, VarBank bank = DEFAULT_BANK);
  static TypedTermList normalize(TypedTermList l, VarBank bank = DEFAULT_BANK);
  static Term* normalize(Term* t, VarBank bank = DEFAULT_BANK);
  static TermList normalize(TermList t, VarBank bank = DEFAULT_BANK);
  friend std::ostream& operator<<(std::ostream& out, Renaming const& self)
  { return out << self._data; }

#if VDEBUG
  void assertValid() const;
  vstring toString() const;
#endif
private:
  class Applicator
  {
  public:
    Applicator(Renaming* parent) : _parent(parent) {}
    TermList apply(unsigned var)
    { return TermList(_parent->getOrBind(var, /* dummy */ DEFAULT_BANK), _parent->bank()); }
  private:
    Renaming* _parent;
  };

  typedef DHMap<unsigned, unsigned, IdentityHash, DefaultHash> VariableMap;
  VariableMap _data;
  unsigned _nextVar;
  bool _identity;
  // we may wish to rename and place on bank simultaneously
  VarBank _bank;
public:
  typedef VariableMap::Item Item;
  VirtualIterator<Item> items() const { return _data.items(); }

};

};

#endif /*__Renaming__*/

