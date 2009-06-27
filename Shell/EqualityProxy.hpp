/**
 * @file EqualityProxy.hpp
 * Defines class EqualityProxy.
 */


#ifndef __EqualityProxy__
#define __EqualityProxy__

#include "../Forwards.hpp"

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
  Options::EqualityProxy _opts;
  bool _rst;
};

};

#endif /* __EqualityProxy__ */
