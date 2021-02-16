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

VTHREAD_LOCAL DHMap<unsigned, unsigned> PersistentGrounding::_splitMap;

PersistentGrounding::PersistentGrounding()
  : _fresh(0), _solver(new MinisatInterfacing(*env->options)) {
  _solveTask = std::thread([&] { this->work(); });
}

PersistentGrounding *PersistentGrounding::instance() {
  static PersistentGrounding *instance = new PersistentGrounding;
  return instance;
}

void PersistentGrounding::work() {
  bool idle = false;
  while(true) {
    // asserting phase
    {
      if(idle)
        std::this_thread::yield();
      std::lock_guard<std::mutex> lock{_lock};
      if(_queue.isEmpty()) {
        // wait for more clauses to come through
        idle = true;
        continue;
      }
      idle = false;
      _solver->ensureVarCount(_fresh);
      while(_queue.isNonEmpty()) {
        SATClause *cl = _queue.pop_front();
        _solver->addClause(cl);
        //std::cout << "received: " << cl->toString() << std::endl;
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

void PersistentGrounding::enqueueClause(Clause *cl) {
  std::lock_guard<std::mutex> lock{_lock};
  //std::cout << "clause: " << cl->toString() << std::endl;

  SATLiteralStack satLiterals;
  {
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
      satLiterals.push(SATLiteral(*var, ground->isPositive()));
    }
  }

  // splits are already ground
  // but: need treating differently as they might be per-thread
  // note thread-local, because (1) in one thread is not the same as in another
  SATLiteralStack satSplits;
  auto splits = cl->splits();
  if(splits) {
    SplitSet::Iterator it(*splits);
    while(it.hasNext()) {
      SplitLevel split = it.next();
      SATLiteral literal = Splitter::getLiteralFromName(split);
      unsigned *var;
      if(_splitMap.getValuePtr(literal.var(), var)) {
        *var = ++_fresh;
      }
      // (sp1, ... spN) -> L1 \/ ... \/ LN
      // could be read as
      // ¬sp1 \/ ... \/ ¬spN \/ L1 \/ ... \/ LN
      satSplits.push(SATLiteral(*var, literal.isNegative()));
    }
  }

  // enqueue the clause
  {
    SATLiteralStack clause;
    clause.loadFromIterator(SATLiteralStack::BottomFirstIterator(satLiterals));
    clause.loadFromIterator(SATLiteralStack::BottomFirstIterator(satSplits));
    SATClause *grounded = SATClause::fromStack(clause);
    _queue.push_back(grounded);
    //std::cout << "enqueued: " << grounded->toString() << std::endl;
  }
}

void PersistentGrounding::enqueueSATClause(SATClause *cl) {
  std::lock_guard<std::mutex> lock{_lock};
  //std::cout << "SAT clause: " << cl->toString() << std::endl;

  SATLiteralStack clause;
  for(int i = 0; i < cl->length(); i++) {
    SATLiteral literal = cl->literals()[i];
    unsigned *var;
    if(_splitMap.getValuePtr(literal.var(), var)) {
      *var = ++_fresh;
    }
    clause.push(SATLiteral(*var, literal.isPositive()));
  }
  SATClause *grounded = SATClause::fromStack(clause);
  _queue.push_back(grounded);
  //std::cout << "enqueued: " << grounded->toString() << std::endl;
}

} // namespace Saturation
#endif