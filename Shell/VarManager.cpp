
/*
 * File VarManager.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
