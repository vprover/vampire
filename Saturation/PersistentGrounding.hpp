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
 * @file PersistentGrounding.hpp
 * Defines class PersistentGrounding for global grounding across proof attempts
 */

#if VTHREADED
#ifndef __PersistentGrounding__
#define __PersistentGrounding__

#include <mutex>
#include <thread>

#include "Forwards.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Array.hpp"

#include "Shell/Options.hpp"

namespace Saturation {

using namespace Kernel;
using namespace Lib;
using namespace SAT;

class PersistentGrounding {
  CLASS_NAME(PersistentGrounding)
  USE_ALLOCATOR(PersistentGrounding)
public:
  PersistentGrounding();
  static PersistentGrounding *instance();
  void enqueueClause(Clause *);
  void enqueueSATClause(SATClause *);
  void work();
private:

  std::thread _solveTask;
  std::mutex _lock;
  unsigned _fresh;
  DHMap<Literal*, unsigned> _literalMap;
  DArray<List<TermList>*> _sortConstants;
  DArray<TermList> _sortConstantsCommon;
  VTHREAD_LOCAL static DHMap<unsigned, unsigned> _splitMap;
  Deque<SATClause *> _queue;
  SATSolver *_solver;
}; // class PersistentGrounding;
} // namespace Saturation
#endif
#endif
