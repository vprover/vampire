/**
 * @file InterpretationManager.cpp
 * Implements class InterpretationManager.
 */

#include "InterpretationManager.hpp"

namespace Kernel
{

InterpretationManager* InterpretationManager::instance()
{
  static InterpretationManager* inst=0;
  if(inst==0) {
    inst=new TrivialInterpretationManager();
  }
  return inst;
}


}
