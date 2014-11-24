/**
 * @file VarManager.cpp
 * Implements class VarManager.
 */

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "VarManager.hpp"

namespace Shell
{

using namespace std;

VarManager::VarFactory* VarManager::_fact = 0;

unsigned VarManager::getVarAlias(unsigned var)
{
  CALL("VarManager::getVarAlias");
  ASS(_fact);

  return _fact->getVarAlias(var);
}

vstring VarManager::getVarName(unsigned var)
{
  CALL("VarManager::getVarName");
  ASS(_fact);

  return _fact->getVarName(var);
}

}
