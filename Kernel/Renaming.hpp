/**
 * @file Renaming.hpp
 * Defines class Renaming
 *
 */

#ifndef __Renaming__
#define __Renaming__

#include "../Lib/DHMap.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class Renaming {
public:
  Renaming() :
    _nextVar(0) {
  }
  unsigned getOrBind(unsigned v) {
    if (_data.insert(v, _nextVar)) {
      return _nextVar++;
    }
    return _data.get(v);
  }
  unsigned apply(unsigned v) const {
    unsigned res;
    if (_data.find(v, res)) {
      return res;
    }
    return v;
  }
  Literal* apply(Literal* l) const;
  TermList apply(TermList l) const;
  bool identity() const;

  static void normalizeVariables(const Term* t, Renaming& res);
  static void inverse(const Renaming& orig, Renaming& target);

#ifdef VDEBUG
  void assertValid() const;
#endif
private:
  typedef DHMap<unsigned, unsigned> VariableMap;
  VariableMap _data;
  int _nextVar;
};

}
;

#endif /*__Renaming__*/

