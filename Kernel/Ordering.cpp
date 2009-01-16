/**
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/Exception.hpp"
#include "../Shell/Options.hpp"

#include "Ordering.hpp"
#include "KBO.hpp"

using namespace Lib;
using namespace Kernel;


Ordering* Ordering::instance()
{
  static Ordering* inst=0;

  if(!inst) {
    switch(env.options->symbolPrecedence()) {
    case Shell::Options::BY_ARITY:
      inst=KBO::createArityPreferenceConstantLevels();
      break;
    case Shell::Options::BY_OCCURRENCE:
      inst=KBO::createReversedAgePreferenceConstantLevels();
      break;
    default:
      NOT_IMPLEMENTED;
    }
  }
  return inst;
}
