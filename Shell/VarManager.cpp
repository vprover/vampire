/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file VarManager.cpp
 * Implements class VarManager.
 */

#include <string>

#include "Debug/Assertion.hpp"

#include "VarManager.hpp"

namespace Shell
{

using namespace std;

VarManager::VarFactory* VarManager::_fact = 0;

unsigned VarManager::getVarAlias(unsigned var)
{
  ASS(_fact);

  return _fact->getVarAlias(var);
}

std::string VarManager::getVarName(unsigned var)
{
  ASS(_fact);

  return _fact->getVarName(var);
}

}
