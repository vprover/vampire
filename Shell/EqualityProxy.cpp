/**
 * @file EqualityProxy.cpp
 * Implements class EqualityProxy.
 */

#include "../Lib/Environment.hpp"
#include "../Kernel/Signature.hpp"

#include "EqualityProxy.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

int EqualityProxy::s_proxyPredicate = 0;

EqualityProxy::EqualityProxy()
: _opts(env.options->equalityProxy())
{
  switch (_opts) {
  case Options::EP_R:
  case Options::EP_RS:
  case Options::EP_RST:
    _rst = true;
    break;
  default:
    _rst = false;
    break;
  }

}


void EqualityProxy::apply(UnitList*& units)
{

}


}
