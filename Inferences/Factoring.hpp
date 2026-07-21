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
 * @file Factoring.hpp
 * Defines class Factoring.
 */


#ifndef __Factoring__
#define __Factoring__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "ProofExtra.hpp"

namespace Inferences {

class Factoring
: public GeneratingInferenceEngine
{
public:
  Factoring(SaturationAlgorithm& salg) : _salg(salg) {}
  ClauseIterator generateClauses(Kernel::Clause* premise) override;
private:
  class ResultsFn;
  const SaturationAlgorithm& _salg;
};

using FactoringExtra = TwoLiteralInferenceExtra;

};

#endif /* __Factoring__ */
