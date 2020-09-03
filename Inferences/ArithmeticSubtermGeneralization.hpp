#ifndef __ARITHMETIC_SUBTERM_GENERALIZATION__
#define __ARITHMETIC_SUBTERM_GENERALIZATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"


namespace Inferences {

class NumeralMultiplicationGeneralization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(NumeralMultiplicationGeneralization);
  USE_ALLOCATOR(NumeralMultiplicationGeneralization);

  NumeralMultiplicationGeneralization() {}
  virtual ~NumeralMultiplicationGeneralization();

  Clause* simplify(Clause* cl);
};


class VariableMultiplicationGeneralization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(VariableMultiplicationGeneralization);
  USE_ALLOCATOR(VariableMultiplicationGeneralization);

  VariableMultiplicationGeneralization() {}
  virtual ~VariableMultiplicationGeneralization();

  Clause* simplify(Clause* cl);
};


class AdditionGeneralization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(AdditionGeneralization);
  USE_ALLOCATOR(AdditionGeneralization);

  AdditionGeneralization() {}
  virtual ~AdditionGeneralization();

  Clause* simplify(Clause* cl);
};

};


#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
