/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ARITHMETIC_SUBTERM_GENERALIZATION__
#define __ARITHMETIC_SUBTERM_GENERALIZATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Lib/Stack.hpp"


namespace Inferences {

class NumeralMultiplicationGeneralization
: public SimplifyingGeneratingInferenceEngine1
{
public:
  ~NumeralMultiplicationGeneralization() override;

  SimplifyingGeneratingInferenceEngine1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class VariableMultiplicationGeneralization
: public SimplifyingGeneratingInferenceEngine1
{
public:
  ~VariableMultiplicationGeneralization() override;

  SimplifyingGeneratingInferenceEngine1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class VariablePowerGeneralization
: public SimplifyingGeneratingInferenceEngine1
{
public:
  ~VariablePowerGeneralization() override;

  SimplifyingGeneratingInferenceEngine1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class AdditionGeneralization
: public SimplifyingGeneratingInferenceEngine1
{
public:
  ~AdditionGeneralization() override;

  SimplifyingGeneratingInferenceEngine1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};

Stack<SimplifyingGeneratingInferenceEngine1*> allArithmeticSubtermGeneralizations();


} // namespace Inferences


#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
