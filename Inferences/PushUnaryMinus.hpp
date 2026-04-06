/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __PUSH_UNARY_MINUS_H__
#define __PUSH_UNARY_MINUS_H__

#include "Forwards.hpp"

#include "Kernel/PolynomialNormalizer.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class PushUnaryMinus
: public ImmediateSimplificationEngine
{
public:
  ~PushUnaryMinus() override;

  Clause* simplify(Clause* cl) override;
};

};

#endif /* __PUSH_UNARY_MINUS_H__ */

