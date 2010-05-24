/**
 * @file Renaming.hpp
 * Defines class Renaming
 *
 */

#ifndef __Renaming__
#define __Renaming__

#if VDEBUG
#include<string>
#endif

#include "Lib/DHMap.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class Renaming {
public:
  Renaming() :
    _nextVar(0) {
  }

  void reset()
  {
    _data.reset();
    _nextVar=0;
  }

  unsigned getOrBind(unsigned v)
  {
    if (_data.insert(v, _nextVar)) {
      return _nextVar++;
    }
    return _data.get(v);
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

#if VDEBUG
  void assertValid() const;
  string toString() const;
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
public:
  typedef VariableMap::Item Item;
  VirtualIterator<Item> items() const { return _data.items(); }

};

};

#endif /*__Renaming__*/

