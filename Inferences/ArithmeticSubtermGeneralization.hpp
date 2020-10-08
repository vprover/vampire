#ifndef __ARITHMETIC_SUBTERM_GENERALIZATION__
#define __ARITHMETIC_SUBTERM_GENERALIZATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Lib/Stack.hpp"
#include "PolynomialNormalization.hpp"


namespace Inferences {

class NumeralMultiplicationGeneralization
: public MaybeImmediateSimplification
{
public:
  CLASS_NAME(NumeralMultiplicationGeneralization);
  USE_ALLOCATOR(NumeralMultiplicationGeneralization);

  virtual ~NumeralMultiplicationGeneralization();

  pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck);
};


class VariableMultiplicationGeneralization
: public MaybeImmediateSimplification
{
public:
  CLASS_NAME(VariableMultiplicationGeneralization);
  USE_ALLOCATOR(VariableMultiplicationGeneralization);

  virtual ~VariableMultiplicationGeneralization();

  pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck);
};


class VariablePowerGeneralization
: public MaybeImmediateSimplification
{
public:
  CLASS_NAME(VariablePowerGeneralization);
  USE_ALLOCATOR(VariablePowerGeneralization);

  virtual ~VariablePowerGeneralization();

  pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck);
};


class AdditionGeneralization
: public MaybeImmediateSimplification
{
public:
  CLASS_NAME(AdditionGeneralization);
  USE_ALLOCATOR(AdditionGeneralization);

  virtual ~AdditionGeneralization();

  pair<Clause*, bool> simplify(Clause* cl, bool doOrderingCheck);
};

Stack<MaybeImmediateSimplification*> allArithmeticSubtermGeneralizations();


} // namespace Inferences


#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
