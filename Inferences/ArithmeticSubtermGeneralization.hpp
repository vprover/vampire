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
: public SimplifyingGeneratingInference1
{
public:
  ~NumeralMultiplicationGeneralization() override;

  SimplifyingGeneratingInference1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class VariableMultiplicationGeneralization
: public SimplifyingGeneratingInference1
{
public:
  ~VariableMultiplicationGeneralization() override;

  SimplifyingGeneratingInference1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class VariablePowerGeneralization
: public SimplifyingGeneratingInference1
{
public:
  ~VariablePowerGeneralization() override;

  SimplifyingGeneratingInference1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};


class AdditionGeneralization
: public SimplifyingGeneratingInference1
{
public:
  ~AdditionGeneralization() override;

  SimplifyingGeneratingInference1::Result simplify(Clause* cl, bool doOrderingCheck) override;
};

Stack<SimplifyingGeneratingInference1*> allArithmeticSubtermGeneralizations();


} // namespace Inferences


#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
