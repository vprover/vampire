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
  Clause* apply(Clause* cl);
  void apply(UnitList*& units);

private:
  class NLiteralTransformer;
  class NFormulaTransformer;
  class NFormulaUnitTransformer;

  static bool isTrivialInterpretation(Interpretation itp);
};

}

#endif // __InterpretedNormalizer__
