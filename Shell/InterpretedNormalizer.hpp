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
  InterpretedNormalizer();
  ~InterpretedNormalizer();

  void apply(Problem& prb);

private:
  bool apply(UnitList*& units);
  Clause* apply(Clause* cl);

  class FunctionTranslator;
  class SuccessorTranslator;
  class BinaryMinusTranslator;

  class RoundingFunctionTranslator;

  class IneqTranslator;
  class NLiteralTransformer;
  class NFormulaTransformer;
  class NFormulaUnitTransformer;

  static bool isTrivialInterpretation(Interpretation itp);

  NLiteralTransformer* _litTransf;
};

}

#endif // __InterpretedNormalizer__
