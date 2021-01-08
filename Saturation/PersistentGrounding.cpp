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

#include "Indexing/TermSharing.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Renaming.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/SATClause.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"

using namespace Kernel;
using namespace SAT;

namespace Saturation {

VTHREAD_LOCAL DHMap<unsigned, unsigned> PersistentGrounding::_splitMap;

PersistentGrounding::PersistentGrounding()
    : _fresh(0), _solver(new MinisatInterfacing(*env->options))
{
  CALL("PersistentGrounding()");

  _sortConstants.ensure(env->sorts->count());
  _sortConstantsCommon.ensure(env->sorts->count());

  for(int i=0 ; i< env->sorts->count(); i++){  _sortConstants[i] =  0; }

  ZIArray<unsigned> constants;
  for(int i = 0; i < env->signature->functions(); i++) {
    Signature::Symbol *fun = env->signature->getFunction(i);
    if(fun->typeCon() || fun->super() || fun->arity() != 0) {
      continue;
    }
    OperatorType *type = fun->fnType();
    Term *result = type->result().term();
    unsigned sort = result->getId();
    unsigned usage = fun->usageCnt();
    unsigned best = constants[sort];
    if(!best || env->signature->getFunction(best)->usageCnt() < usage) {
      constants[sort] = i;
    }
    Term* c = Term::createConstant(i); 
    List<TermList>::push(TermList(c),_sortConstants[sort]);
  }
  for(int i = 0; i < env->sorts->count(); i++) {
    if(constants[i]) {
      _sortConstantsCommon[i].setTerm(Term::create(constants[i], 0, nullptr));
    }
    else {
      _sortConstantsCommon[i].makeVar(0);
    }
  }
  _solveTask = std::thread([&] { this->work(); });
}

PersistentGrounding *PersistentGrounding::instance()
{
  CALL("PersistentGrounding::instance()");
  static PersistentGrounding *instance = new PersistentGrounding;
  return instance;
}

void PersistentGrounding::work()
{
  CALL("PersistentGrounding::work()");
  bool idle = false;
  while (true) {
    // asserting phase
    {
      if (idle)
        std::this_thread::yield();
      std::lock_guard<std::mutex> lock(_lock);
      if (_queue.isEmpty()) {
        // wait for more clauses to come through
        idle = true;
        continue;
      }
      idle = false;
      _solver->ensureVarCount(_fresh);
      while (_queue.isNonEmpty()) {
        SATClause *cl = _queue.pop_front();
        _solver->addClause(cl);
        //std::cout << "received: " << cl->toString() << std::endl;
      }
    }
    // solving phase
    // std::cout << "solving..." << std::endl;
    if (_solver->solve() == SAT::SATSolver::Status::UNSATISFIABLE) {
      std::cout << "% SZS status PersistentlyUnsat" << std::endl;
      std::quick_exit(0);
      break;
    }
  }
}

 // Struct for doing mapping
 struct MapTo {
   MapTo(TermList t) : _t(t) {}
   TermList _t;
   TermList apply(unsigned var)
   {
        return _t;
   }
 };



void PersistentGrounding::enqueueClause(Clause *cl)
{
  CALL("PersistentGrounding::enqueueClause()");
  std::lock_guard<std::mutex> lock{_lock};
  //std::cout << "clause: " << cl->toString() << std::endl;


  static Shell::Options::GroundingChoice choice = env->options->persistentGroundingChoice();
  //TODO - Currently hacked so only FRESH works with sorts 
  if(env->sorts->count() != 1){
    choice = Options::GroundingChoice::FRESH;
  }
  List<TermList>* grounders = 0;

  switch(choice){
    case Options::GroundingChoice::FRESH:
    {
       TermList t;
       t.makeVar(0);
       List<TermList>::push(t,grounders);
       break;
    }
    case Options::GroundingChoice::COMMON:
    {
       List<TermList>::push(_sortConstantsCommon[0],grounders);
       break;
    } 
    case Options::GroundingChoice::INPUT:
    {
      grounders = _sortConstants[0];
      break;
    }
    default:
      NOT_IMPLEMENTED;
  }

  List<TermList>::Iterator it(grounders);

  while(it.hasNext()){
    TermList g = it.next();

    SATLiteralStack satLiterals;
    {
      // for regular literals, map them to ground literals
      for (int i = 0; i < cl->length(); i++) {
        Literal *lit = cl->literals()[i];
        MapTo map(g);
        Literal *grounded = SubstHelper::apply(lit, map);
        Literal *positive = Literal::positiveLiteral(grounded);
        unsigned *var;
        if (_literalMap.getValuePtr(positive, var)) {
          *var = ++_fresh;
        }
        satLiterals.push(SATLiteral(*var, grounded->isPositive()));
      }
    }

    // splits are already ground
    // but: need treating differently as they might be per-thread
    // note thread-local, because (1) in one thread is not the same as in another
    SATLiteralStack satSplits;
    auto splits = cl->splits();
    if (splits) {
      SplitSet::Iterator it(*splits);
      while (it.hasNext()) {
        SplitLevel split = it.next();
        SATLiteral literal = Splitter::getLiteralFromName(split);
        unsigned *var;
        if (_splitMap.getValuePtr(literal.var(), var)) {
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
}

void PersistentGrounding::enqueueSATClause(SATClause *cl)
{
  CALL("PersistentGrounding::enqueueSATClause()");
  std::lock_guard<std::mutex> lock{_lock};
  //std::cout << "SAT clause: " << cl->toString() << std::endl;

  SATLiteralStack clause;
  for (int i = 0; i < cl->length(); i++) {
    SATLiteral literal = cl->literals()[i];
    unsigned *var;
    if (_splitMap.getValuePtr(literal.var(), var)) {
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
