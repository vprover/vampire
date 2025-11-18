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
 * @file GlobalSubsumption.cpp
 * Implements class GlobalSubsumption.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Grounder.hpp"
#include "Kernel/Inference.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/MinisatInterfacing.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "GlobalSubsumption.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

GlobalSubsumption::GlobalSubsumption(const Options& opts) :
  _solver(new ProofProducingSATSolver(new MinisatInterfacing)),
  _grounder(new GlobalSubsumptionGrounder(*_solver)),
  _randomizeMinim(opts.randomTraversals())
{}

void GlobalSubsumption::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
}

void GlobalSubsumption::detach()
{
  ForwardSimplificationEngine::detach();
}

/**
 * Perform GS on cl and return the reduced clause,
 * or cl itself if GS does not reduce.
 *
 * If reduced, initialize prems with reduction premises (including cl).
 */
Clause* GlobalSubsumption::perform(Clause* cl, Stack<Unit*>& prems)
{
  TIME_TRACE("global subsumption");

  if(cl->color()==COLOR_LEFT) {
    return cl;
  }

  // SAT literals of the prop. abstraction of cl
  static SATLiteralStack plits;
  plits.reset();

  // assumptions corresponding to the negation of the new prop clause
  // (and perhaps additional ones used to "activate" AVATAR-conditional clauses)
  static SATLiteralStack assumps;
  assumps.reset();

  // lookup to retrieve the FO lits later back
  static DHMap<SATLiteral,Literal*> lookup;
  lookup.reset();

  // first abstract cl's FO literals using grounder,
  // start filling assumps and initialize lookup
  _grounder->groundNonProp(cl, plits);

  unsigned clen = plits.size();
  for (unsigned i = 0; i < clen; i++) {
    lookup.insert(plits[i],(*cl)[i]);
    assumps.push(plits[i].opposite());
  }

  // then add literals corresponding to cl's split levels
  //
  // also keep filling assumps for gsaa=crom_curent
  if (cl->splits() && cl->splits()->size()!=0) {
    auto sit = cl->splits()->iter();
    while(sit.hasNext()) {
      SplitLevel l = sit.next();
      unsigned var = splitLevelToVar(l);

      plits.push(SATLiteral(var,false)); // negative
      assumps.push(SATLiteral(var,true)); // positive
    }
  }

  // Would be nice to have this:
  // ASS_NEQ(solver.solve(_uprOnly),SATSolver::UNSATISFIABLE);
  // But even if the last addition made the SAT solver's content unconditionally inconsistent
  // the last call to solveUnderAssumptions might have missed that

  // create SAT clause and add to solver
  SATClause* scl = SATClause::fromStack(plits);
  SATInference* inf = new FOConversionInference(cl);
  scl->setInference(inf);
  _solver->addClause(scl);

  // check for subsuming clause by looking for a subset of used assumptions
  Status res = _solver->solveUnderAssumptions(assumps, /* onlyPropagate = */ true);

  if (res == Status::UNSATISFIABLE) {
    // it should always be UNSAT with full assumps,
    // but we may not get that far with limited solving power (_uprOnly)

    SATLiteralStack failed = _solver->failedAssumptions();

    if (failed.size() < assumps.size()) {
      // proper subset sufficed for UNSAT - that's the interesting case
      SATLiteralStack failedFinal = _solver->explicitlyMinimizedFailedAssumptions(/* onlyPropagate = */ true, _randomizeMinim);

      static LiteralStack survivors;
      survivors.reset();

      static Set<SATLiteral> splitAssumps;
      splitAssumps.reset();

      for (unsigned i = 0; i < failedFinal.size(); i++) {
        SATLiteral olit = failedFinal[i].opposite(); // back to the original polarity

        Literal* lit;
        if (lookup.find(olit,lit)) { // lookup the corresponding FO literal
          survivors.push(lit);
        } else { // otherwise it was a split level assumption
          splitAssumps.insert(olit);
        }
      }

      // TODO: what about GS being proper only on the split level assumption side? (But then it is not a reduction from the FO perspective!)

      // this is the main check -- whether we have a proper subclause (no matter the split level assumptions)
      if (survivors.size() < clen) {
        RSTAT_MCTR_INC("global_subsumption_by_number_of_removed_literals",clen-survivors.size());

        SATClauseList *allSATPrems = _solver->premiseList();
        ASS(allSATPrems)

        prems.reset();
        prems.push(cl);

        for(SATClause *satPrem : iterTraits(allSATPrems->iter()))
          SATInference::collectFilteredFOPremises(satPrem, prems,
            // allSATPrems must be filtered since a derived clause cannot depend on inactive splits
            [this] (SATClause* prem) {
              // don't keep any premise which mentions an unassumed split level assumption
              unsigned prem_sz = prem->size();
              for (unsigned i = 0; i < prem_sz; i++ ) {
                SATLiteral lit = (*prem)[i];
                SplitLevel lev;
                if (isSplitLevelVar(lit.var(),lev)) {
                  ASS(!lit.positive());
                  if (!splitAssumps.contains(lit)) {
                    return false;
                  }
                }
              }
              return true;
            } );

        UnitList* premList = 0;
        Stack<Unit*>::Iterator it(prems);
        while (it.hasNext()) {
          Unit* us = it.next();
          UnitList::push(us, premList);
        }

        Inference inf(NeedsMinimization(InferenceRule::GLOBAL_SUBSUMPTION, premList, allSATPrems, failedFinal));
        // CAREFUL:
        // FromSatRefutation does not automatically propagate age
        inf.setAge(cl->age());
        // also, let's not propagate inputType from the whole big (non-minimized) set of premises (which probably already contains a piece of the conjecture)
        inf.setInputType(cl->inputType());
        // Splitter will set replacement's splitSet, so we don't have to do it here

        Clause* replacement = Clause::fromIterator(LiteralStack::BottomFirstIterator(survivors),inf);

        ASS_L(replacement->length(), clen);

        return replacement;
      }
    }
  }

  return cl;
}

/**
 * Functor that extracts a clause from UnitSpec.
 */
struct GlobalSubsumption::Unit2ClFn
{
  Clause* operator() (Unit* us) {
    return us->asClause();
  }
};

bool GlobalSubsumption::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  static Stack<Unit*> prems;

  Clause* newCl = perform(cl,prems);
  if(newCl==cl) {
    return false;
  }

  Stack<Unit*>::BottomFirstIterator it(prems);

  replacement = newCl;
  premises = pvi( getMappingIterator(it, Unit2ClFn()) );
  return true;
}

}
