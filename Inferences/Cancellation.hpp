/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __CANCELLATION_HPP__
#define __CANCELLATION_HPP__
#include "Inferences/InferenceEngine.hpp"

namespace Inferences {


class Cancellation
: public SimplifyingGeneratingLiteralSimplification
{
public:
  Cancellation(Ordering& ordering);
  ~Cancellation() override;

  Result simplifyLiteral(Literal*) override;
};



} // namespace Inferences
#endif /* __CANCELLATION_HPP__ */
