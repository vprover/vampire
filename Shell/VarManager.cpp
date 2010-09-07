/**
 * @file VarManager.cpp
 * Implements class VarManager.
 */

#include "Debug/Assertion.hpp"

#include "VarManager.hpp"

namespace Shell
{

VarManager::VarFactory* VarManager::_fact = 0;

unsigned VarManager::getVarAlias(unsigned var)
{
  CALL("VarManager::getVarAlias");
  ASS(_fact);

  return _fact->getVarAlias(var);
}

}
