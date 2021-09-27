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
#include "Shell/SMTPrinter.hpp"

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
  void onNonRedundantClause(Clause* c);
  void onParenthood(Clause* cl, Clause* parent);

private:
  void outputSymbolElimination(Clause* c);

  /**
   * all transparent clauses with coloured parents generated recently
   * not output until shown not to be redundant in onNonRedundantClause
   *
   * reset in onAllProcessed
   */
  DHSet<Clause *> _eliminated;

  /**
   * Final cache to prevent duplicate output
   * Key by string as clauses are not shared
   */
  DHSet<vstring> _alreadyPrinted;

  SaturationAlgorithm* _sa;
  Shell::SMTPrinter _printer;
};

}

#endif // __SymElOutput__
