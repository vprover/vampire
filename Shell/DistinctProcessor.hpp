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
 * @file DistinctProcessor.hpp
 * Defines class DistinctProcessor.
 */

#ifndef __DistinctProcessor__
#define __DistinctProcessor__

#include "Forwards.hpp"

#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/Problem.hpp"

namespace Shell {

using namespace Kernel;
using namespace Lib;

/**
 * Registers top-level distinct predicates in the Signature. Should be
 * therefore called only with formulas that are valid.
 */
class DistinctProcessor : public ScanAndApplyFormulaUnitTransformer {
public:

  using ScanAndApplyFormulaUnitTransformer::apply;

  static bool isDistinctPred(Literal* l);

protected:
  virtual bool apply(FormulaUnit* unit, Unit*& res);
  virtual bool apply(Clause* cl, Unit*& res);

  virtual void updateModifiedProblem(Problem& prb)
  {
    CALL("DistinctProcessor::updateModifiedProblem");
    prb.invalidateProperty();
  }
};

}

#endif // __DistinctProcessor__
