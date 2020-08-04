
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
