/**
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include "../Forwards.hpp"

#include "../Lib/SmartPtr.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Exception.hpp"
#include "../Shell/Options.hpp"

#include "Ordering.hpp"
#include "KBO.hpp"

using namespace Lib;
using namespace Kernel;


Ordering* Ordering::instance()
{
  static OrderingSP inst;

  if(!inst) {
    switch(env.options->symbolPrecedence()) {
    case Shell::Options::BY_ARITY:
      inst=OrderingSP(KBO::createArityPreferenceConstantLevels());
      break;
    case Shell::Options::BY_OCCURRENCE:
      inst=OrderingSP(KBO::createReversedAgePreferenceConstantLevels());
      break;
    default:
      NOT_IMPLEMENTED;
    }
  }
  return inst.ptr();
}
