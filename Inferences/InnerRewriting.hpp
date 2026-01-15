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
 * @file InnerRewriting.hpp
 * Defines class InnerRewriting.
 */

#ifndef __InnerRewriting__
#define __InnerRewriting__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;

// TODO this should be an immediate simplification
class InnerRewriting
: public ImmediateSimplificationEngine
{
public:
  InnerRewriting(const Ordering& ord) : _ord(ord) {}

  Clause* simplify(Clause* cl) override;

private:
  const Ordering& _ord;
};

};

#endif // __InnerRewriting__
