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
 * @file SymElOutput.hpp
 * Defines class SymElOutput.
 */

#ifndef __SymElOutput__
#define __SymElOutput__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Shell/TPTPPrinter.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

/**
 * The @b SymElOutput object takes care of the output of
 * the consequences of symbol eliminating inferences
 */
class SymElOutput {
public:
  CLASS_NAME(SymElOutput);
  USE_ALLOCATOR(SymElOutput);
  
  SymElOutput();

  void init(SaturationAlgorithm* sa);

  void onAllProcessed();
  void onInputClause(Clause* c);
  void onNonRedundantClause(Clause* c);
  void onParenthood(Clause* cl, Clause* parent);


private:

  void onSymbolElimination(Color eliminated, Clause* c, bool nonRedundant=false);

  void outputSymbolElimination(Color eliminated, Clause* c);

  void checkForPreprocessorSymbolElimination(Clause* cl);

  /** Number that would be used for the next symbol-eliminating
   * inference conclusion that is output */
  unsigned _symElNextClauseNumber;

  /**
   * Contains record of rewrites on symbol-eliminating clauses
   *
   * Is reset in the call to the @b onAllProcessed method.
   *
   * It is used so that we output symbol eliminating clauses
   * after they are simplified and shown to be non-redundant.
   */
  DHMap<Clause*,Clause*> _symElRewrites;

  /**
   * Contains record of colors that were aliminated in
   * symbol-eliminating clauses
   *
   * Is reset in the call to the @b onAllProcessed method.
   */
  DHMap<Clause*,Color> _symElColors;


  SaturationAlgorithm* _sa;

  TPTPPrinter _printer;
};

}

#endif // __SymElOutput__
