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
 * @file LeibnizEqualityElimination.hpp
 * Defines class LeibnizEqualityElimination.
 */

#ifndef __LeibnizEqualityElimination__
#define __LeibnizEqualityElimination__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

/**
 * Using Leibniz's rule, that is, ∀ x,y. (x ≈ y <=> ∀ p. (p x <=> p y)),
 * implements the following generating inference:
 *
 *                     X s ≈ ⊤ v X t ≈ ⊥ v C
 *             --------------------------------------
 *                    (s ≈ t v C){ X ↦ (eq s) }
 *                (s ≈ t v C){ X ↦ λ x. ¬(eq x t) }
 *
 * Note that eq denotes the equality proxy in the above rule.
 * See unit tests for instances of the rule.
 */
class LeibnizEqualityElimination
  : public GeneratingInferenceEngine
{
public:
  LeibnizEqualityElimination(SaturationAlgorithm&) {}
  ClauseIterator generateClauses(Clause* premise) override;
};

}

#endif
