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
 * @file FunctionDefinitionDiscovery.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __FunctionDefinitionDiscovery__
#define __FunctionDefinitionDiscovery__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Lib/STL.hpp"

#include "InductionPreprocessor.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

class FunctionDefinitionDiscovery {
public:
  FunctionDefinitionDiscovery() : foundFunctionDefinitions(1) {}

  void findPossibleRecursiveDefinitions(Formula* f, vvector<Formula*> conditions);
  void addBestConfiguration();

private:
  vvector<vmap<unsigned, pair<InductionTemplate, vvector<pair<Literal*,bool>>>>> foundFunctionDefinitions;
  vmap<unsigned, InductionTemplate> foundPredicateDefinitions;
};

} // Shell

#endif
