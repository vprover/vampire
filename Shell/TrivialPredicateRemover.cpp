
/*
 * File TrivialPredicateRemover.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TrivialPredicateRemover.cpp
 * Implements class TrivialPredicateRemover.
 */

#include "Lib/ArrayMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Options.hpp"

#include "PredicateDefinition.hpp"
#include "Statistics.hpp"

#include "TrivialPredicateRemover.hpp"


namespace Shell
{

TrivialPredicateRemover::TrivialPredicateRemover() : _processedProblem(0) {}

void TrivialPredicateRemover::apply(Problem& prb)
{
  CALL("TrivialPredicateRemover::apply(Problem&)");

  ScopedLet<Problem*> prbLet(_processedProblem, &prb);
  if(apply(prb.units())) {
    prb.invalidateByRemoval();
  }
}

bool TrivialPredicateRemover::apply(UnitList*& units)
{
  CALL("TrivialPredicateRemover::apply");

  TimeCounter tc(TC_TRIVIAL_PREDICATE_REMOVAL);

  scan(units);

  bool modified = false;

  UnitList::DelIterator dit(units);
  while(dit.hasNext()) {
    Clause* cl = static_cast<Clause*>(dit.next());
    if(_removed.contains(cl) && 
       !(cl->isGoal() && env.options->ignoreConjectureInPreprocessing())) {
      dit.del();
      modified = true;
    }
  }
  return modified;
}

void TrivialPredicateRemover::scan(UnitList* units)
{
  CALL("TrivialPredicateRemover::scan");

  unsigned preds = env.signature->predicates();
  _posOcc.init(preds, 0);
  _negOcc.init(preds, 0);
  _predClauses.ensure(preds);


  for(unsigned i=0; i<preds; i++) {
    if(env.signature->getPredicate(i)->protectedSymbol()) {
      //we add a fictional positive and negative occurrence to protected
      //predicates, so that they are never considered trivial
      _posOcc[i]++;
      _negOcc[i]++;
    }
  }

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS(u->isClause());
    Clause* cl = static_cast<Clause*>(u);
    count(cl, 1);
  }

  Stack<unsigned> toDo;

  for(unsigned i=0; i<preds; i++) {
    if(_posOcc[i]==0 || _negOcc[i]==0) {
      toDo.push(i);
    }
  }

  ASS(_reachedZeroes.isEmpty());

  while(toDo.isNonEmpty()) {
    unsigned removedPred = toDo.pop();
    if(_predClauses[removedPred].size()==0) {
      ASS_EQ(_posOcc[removedPred],0);
      ASS_EQ(_negOcc[removedPred],0);
      continue;
    }
    if(_processedProblem) {
      _processedProblem->addTrivialPredicate(removedPred, _negOcc[removedPred]==0);
    }
    ClauseSet::Iterator cit(_predClauses[removedPred]);
    while(cit.hasNext()) {
      Clause* cl = cit.next();
      if(_removed.contains(cl)) {
	continue;
      }
      _removed.insert(cl);
      count(cl, -1);
      env.statistics->trivialPredicates++;
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] ennf: Removed due to trivial predicate: " 
                << cl->toString() << std::endl;
        env.endOutput();
      }      
    }
    while(_reachedZeroes.isNonEmpty()) {
      unsigned zpred = _reachedZeroes.pop();
      if(zpred!=removedPred) {
	toDo.push(zpred);
      }
    }
  }
}

/**
 * Update predicate occurrence counters with clause @c cl.
 *
 * If we're decreasing counters and a counter reaches zero,
 * its predicate number is added to the @c _reachedZeroes stack.
 */
void TrivialPredicateRemover::count(Clause* cl, int add)
{
  CALL("TrivialPredicateRemover::count");

  //1 - positive, -1 - negative, 0 - both occurrences
  static ArrayMap<int> predOccurrences;
  predOccurrences.ensure(env.signature->predicates());
  predOccurrences.reset();

  static Stack<unsigned> preds;
  preds.reset();

  Clause::Iterator it(*cl);
  while(it.hasNext()) {
    Literal* lit = it.next();
    unsigned pred = lit->functor();
    int val = lit->isPositive() ? 1 : -1;
    if(predOccurrences.find(pred)) {
      if(val!=predOccurrences.get(pred)) {
	predOccurrences.set(pred, 0);
      }
    }
    else {
      predOccurrences.set(pred, val);
      preds.push(pred);
      _predClauses[pred].insert(cl);
    }
  }

  Stack<unsigned>::Iterator pit(preds);
  while(pit.hasNext()) {
    unsigned pred = pit.next();
    int val = predOccurrences.get(pred);
    if(val==0) {
      continue;
    }
    ASS(val==1 || val==-1);
    int& updatedCtr = (val==1) ? _posOcc[pred] : _negOcc[pred];
    if(add<0) {
      ASS_GE(updatedCtr,-add);
      if(updatedCtr==-add) {
	_reachedZeroes.push(pred);
      }
    }
    updatedCtr += add;
  }
}

}
