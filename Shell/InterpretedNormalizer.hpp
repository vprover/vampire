/**
 * @file InterpretedNormalizer.hpp
 * Defines class InterpretedNormalizer.
 */

#ifndef __InterpretedNormalizer__
#define __InterpretedNormalizer__

#include "Forwards.hpp"

#include "Kernel/Theory.hpp"



namespace Shell {

using namespace Kernel;

class InterpretedNormalizer {
public:
  InterpretedNormalizer(Property* prop=0);
  ~InterpretedNormalizer();

  Clause* apply(Clause* cl);
  void apply(UnitList*& units);

private:
  class FunctionTranslator;
  class SuccessorTranslator;
  class BinaryMinusTranslator;

  class IneqTranslator;
  class NLiteralTransformer;
  class NFormulaTransformer;
  class NFormulaUnitTransformer;

  static bool isTrivialInterpretation(Interpretation itp);

  NLiteralTransformer* _litTransf;
};

}

#endif // __InterpretedNormalizer__
