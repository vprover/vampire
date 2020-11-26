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

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class Renaming {
public:
  CLASS_NAME(Renaming);
  USE_ALLOCATOR(Renaming);

  Renaming() :
    _nextVar(0), _identity(true) {
  }

  /*
   * Construct a renaming with names starting at firstVar
   */
  Renaming(unsigned firstVar) :
    _nextVar(firstVar), _identity(true) {
  }

  void reset()
  {
    _data.reset();
    _nextVar = 0;
    _identity = true;
  }

  unsigned getOrBind(unsigned v)
  {
    unsigned res;
    if (_data.findOrInsert(v, res, _nextVar)) {
      _nextVar++;
      if(v!=res) {
	_identity = false;
      }
    }
    return res;
  }
  unsigned get(unsigned v) const
  { return _data.get(v); }
  bool contains(unsigned v)
  { return _data.find(v); }

  Literal* apply(Literal* l);
  Term* apply(Term* l);
  TermList apply(TermList l);
  bool identity() const;

  void normalizeVariables(const Term* t);
  void normalizeVariables(TermList t);
  void makeInverse(const Renaming& orig);

  static Literal* normalize(Literal* l);
  static Term* normalize(Term* t);

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
    { return TermList(_parent->getOrBind(var), false); }
  private:
    Renaming* _parent;
  };

  typedef DHMap<unsigned, unsigned, IdentityHash> VariableMap;
  VariableMap _data;
  unsigned _nextVar;
  bool _identity;
public:
  typedef VariableMap::Item Item;
  VirtualIterator<Item> items() const { return _data.items(); }

};

};

#endif /*__Renaming__*/

