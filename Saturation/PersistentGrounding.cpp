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
 * @file PersistentGrounding.cpp
 * Implements class PersistentGrounding
 */

#if VTHREADED
#include "PersistentGrounding.hpp"

#include "Lib/SharedSet.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SubstHelper.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/SATClause.hpp"
#include "Saturation/Splitter.hpp"

using namespace Kernel;
using namespace SAT;

namespace Saturation {

PersistentGrounding::PersistentGrounding()
  : _solver(new MinisatInterfacing(*env.options)) {
  _solveTask = std::thread([&] { this->work(); });
}

PersistentGrounding *PersistentGrounding::instance() {
  static PersistentGrounding *instance = new PersistentGrounding;
  return instance;
}

void PersistentGrounding::work() {
  while(true) {
    // asserting phase
    {
      std::lock_guard<std::mutex> lock{_queueLock};
      _solver->ensureVarCount(_fresh);
      if(_queue.isEmpty()) {
        // wait for more clauses to come through
        std::this_thread::yield();
        continue;
      }
      while(_queue.isNonEmpty()) {
        SATClause *cl = _queue.pop_front();
        _solver->addClause(cl);
        // std::cout << cl->toString() << std::endl;
      }
    }
    // solving phase
    // std::cout << "solving..." << std::endl;
    if(_solver->solve() == SAT::SATSolver::Status::UNSATISFIABLE) {
      std::cout << "% SZS status PersistentlyUnsat" << std::endl;
      break;
    }
  }
}

void PersistentGrounding::enqueue(Clause *cl) {
  VTHREAD_LOCAL static SATLiteralStack clause;
  clause.reset();

  {
    std::lock_guard<std::mutex> lock{_groundLock};

    // like InstGen: maps all variables to the same distinct term
    class MapToSame
    {
    public:
      TermList apply(unsigned var)
      {
        return TermList(0, false);
      }
    };
    // for regular literals, map them InstGen-style to ground literals
    for(int i = 0; i < cl->length(); i++) {
      MapToSame map;
      Literal *ground = SubstHelper::apply(cl->literals()[i], map);
      Literal *positive = Literal::positiveLiteral(ground);
      unsigned *var;
      if(_literalMap.getValuePtr(positive, var)) {    
        *var = ++_fresh;
      }
      clause.push(SATLiteral(*var, ground->isPositive()));
    }
  }

  // splits are already ground
  // but: need treating differently as they might be per-thread
  VTHREAD_LOCAL static DHMap<unsigned, unsigned> splitMap;
  auto splits = cl->splits();
  if(splits) {
    SplitSet::Iterator it(*splits);
    while(it.hasNext()) {
      SplitLevel split = it.next();
      SATLiteral literal = Splitter::getLiteralFromName(split);
      unsigned *var;
      if(splitMap.getValuePtr(literal.var(), var)) {
        *var = ++_fresh;
      }
      // (sp1, ... spN) -> L1 \/ ... \/ LN
      // could be read as
      // ¬sp1 \/ ... \/ spN \/ L1 \/ ... \/ LN
      // and therefore should be opposite polarity (i.e. isNegative()) below
      // but it doesn't matter and this way is easier to read
      clause.push(SATLiteral(*var, literal.isPositive()));
    }
  }

  std::lock_guard<std::mutex> lock{_queueLock};
  _queue.push_back(SATClause::fromStack(clause));
}

} // namespace Saturation
#endif