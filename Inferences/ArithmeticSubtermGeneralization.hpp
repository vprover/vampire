#ifndef __ARITHMETIC_SUBTERM_GENERALIZATION__
#define __ARITHMETIC_SUBTERM_GENERALIZATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"


namespace Inferences {

class MultiplicationGeneralization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(MultiplicationGeneralization);
  USE_ALLOCATOR(MultiplicationGeneralization);

  MultiplicationGeneralization() {}
  virtual ~MultiplicationGeneralization();

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


// class AdditionGeneralization
// : public ImmediateSimplificationEngine
// {
// public:
//   CLASS_NAME(AdditionGeneralization);
//   USE_ALLOCATOR(AdditionGeneralization);
//
//   AdditionGeneralization() {}
//   virtual ~AdditionGeneralization();
//
//   Clause* simplify(Clause* cl);
// };

};


#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
