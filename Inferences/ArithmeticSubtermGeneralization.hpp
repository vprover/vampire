#ifndef __ARITHMETIC_SUBTERM_GENERALIZATION__
#define __ARITHMETIC_SUBTERM_GENERALIZATION__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"


namespace Inferences {

class ArithmeticSubtermGeneralization
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(ArithmeticSubtermGeneralization);
  USE_ALLOCATOR(ArithmeticSubtermGeneralization);

  ArithmeticSubtermGeneralization() {}
  virtual ~ArithmeticSubtermGeneralization();

  Clause* simplify(Clause* cl);
};

};



#endif // __ARITHMETIC_SUBTERM_GENERALIZATION__
