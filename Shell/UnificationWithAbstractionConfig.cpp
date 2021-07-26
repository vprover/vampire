/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

using namespace Shell;
using namespace Kernel;

bool UnificationWithAbstractionConfig::isInterpreted(TermList t) 
{
  if (t.isVar()) {
    return false;
  } else {
    return isInterpreted(t.term());
  }
}

bool UnificationWithAbstractionConfig::isInterpreted(Term* t) 
{
  return theory->isInterpretedFunction(t) 
    || theory->isInterpretedConstant(t) 
    || env.signature->getFunction(t->functor())->termAlgebraCons();
}
