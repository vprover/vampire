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
 * @file CasesSimp.hpp
 * Defines class CasesSimp.
 */

#ifndef __CASES_SIMP__
#define __CASES_SIMP__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

class CasesSimp
  : public ImmediateSimplificationEngineMany
{
public:
  Option<ClauseIterator> simplifyMany(Clause* premise) override;
};

}

#endif
