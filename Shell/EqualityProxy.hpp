/**
 * @file EqualityProxy.hpp
 * Defines class EqualityProxy.
 */


#ifndef __EqualityProxy__
#define __EqualityProxy__

#include "../Forwards.hpp"

#include "../Kernel/Term.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;


class EqualityProxy
{
public:
  static unsigned s_proxyPredicate;

  EqualityProxy();

  void apply(UnitList*& units);
private:
  void addAxioms(UnitList*& units);
  Clause* apply(Clause* cl);
  Literal* apply(Literal* lit);

  Literal* makeProxyLiteral(bool polarity, TermList arg0, TermList arg1);


  Options::EqualityProxy _opt;
  bool _rst;
};

};

#endif /* __EqualityProxy__ */
