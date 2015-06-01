/**
 * @file GlobalSubsumption.cpp
 * Implements class GlobalSubsumption.
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Metaiterators.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Grounder.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/GroundingIndex.hpp"

#include "SAT/SATClause.hpp"
#include "SAT/SATSolver.hpp"
#include "SAT/SATInference.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "GlobalSubsumption.hpp"

#undef LOGGING
#define LOGGING 0

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void GlobalSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("GlobalSubsumption::attach");

  ASS(!_index);

  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<GroundingIndex*>(
	  _salg->getIndexManager()->request(GLOBAL_SUBSUMPTION_INDEX) );

  if (_salg->getOptions().globalSubsumptionAvatarAssumptions() == Options::GlobalSubsumptionAvatarAssumptions::FULL_MODEL) {
    _splitter=_salg->getSplitter();
  } else {
    _splitter = 0;
  }
}

void GlobalSubsumption::detach()
{
  CALL("GlobalSubsumption::detach");

  _index=0;
  _salg->getIndexManager()->release(GLOBAL_SUBSUMPTION_INDEX);
  ForwardSimplificationEngine::detach();
}

/**
 * Perform GS on cl and return the reduced clause,
 * or cl itself if GS does not reduce.
 * 
 * If reduced, initialize prems with reduction premises (including cl). 
 */
Clause* GlobalSubsumption::perform(Clause* cl, Stack<UnitSpec>& prems)
{
  CALL("GlobalSubsumption::perform/1");

  TimeCounter tc(TC_GLOBAL_SUBSUMPTION);

  if(cl->color()==COLOR_LEFT) {
    return cl;
  }
   
  if(!_avatarAssumptions && cl->splits() && cl->splits()->size()!=0) {
    return cl;
  }
  
  Grounder& grounder = _index->getGrounder();
  SATSolverWithAssumptions& solver = _index->getSolver();

  // SAT literals of the prop. abstraction of cl
  static SATLiteralStack plits;
  plits.reset();
  
  // assumptions corresponding to the negation of the new prop clause
  static SATLiteralStack assumps;
  assumps.reset();
  
  // lookup to retrieve the FO lits later back
  static DHMap<SATLiteral,Literal*> lookup;
  lookup.reset();
    
  // first abstract cl's FO literals using grounder,
  // start filling assumps and initialize lookup
  grounder.groundNonProp(cl, plits, false);
  
  unsigned clen = plits.size();    
  for (unsigned i = 0; i < clen; i++) {
    lookup.insert(plits[i],(*cl)[i]);
    assumps.push(plits[i].opposite());
  }
    
  // then add literals corresponding to cl's split levels,
  // and keep filling assumps
  if (cl->splits() && cl->splits()->size()!=0) {
    ASS(_avatarAssumptions);
    
    SplitSet::Iterator sit(*cl->splits());
    while(sit.hasNext()) {
      SplitLevel l = sit.next();
      
      unsigned* pvar;
      if(_levels2vars.getValuePtr(l, pvar)) {    
        *pvar = solver.newVar();
        ALWAYS(_vars2levels.insert(*pvar,l));
      }
      
      plits.push(SATLiteral(*pvar,false)); // negative
      assumps.push(SATLiteral(*pvar,true)); // positive
    }
  }
  
  ASS_NEQ(solver.solve(_uprOnly),SATSolver::UNSATISFIABLE);

  // create SAT clause and add to solver
  SATClause* scl = SATClause::fromStack(plits);
  SATInference* inf = new FOConversionInference(UnitSpec(cl));
  scl->setInference(inf);
  solver.addClause(scl);

  // check for subsuming clause looking for a proper subset of used assumptions
  SATSolver::Status res = solver.solveUnderAssumptions(assumps, _uprOnly, true /* only proper subsets */);

  if (res == SATSolver::UNSATISFIABLE) { 
    // it should always be UNSAT with full assumps,
    // but we may not get that far with limited solving power (_uprOnly)    
    
    const SATLiteralStack& failed = solver.failedAssumptions();

    if (failed.size() < assumps.size()) {
      // proper subset sufficed for UNSAT - that's the interesting case
      
      const SATLiteralStack& failedFinal = _explicitMinim ? solver.explicitlyMinimizedFailedAssumptions(_uprOnly,_randomizeMinim) : failed;

      static LiteralStack survivors;
      survivors.reset();

      for (unsigned i = 0; i < failedFinal.size(); i++) {
        Literal* lit;
        if (lookup.find(failedFinal[i].opposite(),lit)) { // back to the original polarity to lookup the corresponding FO literal
          survivors.push(lit);
        } // otherwise it was a split level assumption
      }

      // this is the main check -- whether we have a proper subclause (no matter the split level assumptions)
      if (survivors.size() < clen) {                
        SATClause* ref = solver.getRefutation(); // aren't we leaking the refutation clause with Minisat and Lingeling?       

        prems.reset();

        prems.push(UnitSpec(cl));
        SATInference::collectFilteredFOPremises(ref, prems,
          [this,cl] (SATClause* prem) {
            // don't keep any premise which mentions an unassumed split level assumption
            unsigned prem_sz = prem->size();
            for (unsigned i = 0; i < prem_sz; i++ ) {
              SATLiteral lit = (*prem)[i];
              SplitLevel lev;
              if (_vars2levels.find(lit.var(),lev)) {
                ASS(lit.isNegative());                
                // TODO: adapt to full_model option
                if (!cl->splits()->member(lev)) {
                  return false;
                }
              }
            }
            return true;
          } );
        
        UnitList* premList = 0;
        Stack<UnitSpec>::Iterator it(prems); 
        while (it.hasNext()) {
          UnitSpec us = it.next();
          UnitList::push(us.unit(), premList);
        }
        
        Inference* inf = new InferenceMany(Inference::GLOBAL_SUBSUMPTION, premList);
        Clause* replacement = Clause::fromIterator(LiteralStack::BottomFirstIterator(survivors),cl->inputType(), inf);
           
        replacement->setAge(cl->age());
        // Splitter will set replacement's splitSet, so we don't have to do it here
        
        // TODO: However, it will depend on the premises collected abowe
        // and with silly implementation of solver.getRefutation()
        // there will be many of them

        env.statistics->globalSubsumption++;
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
struct GlobalSubsumption::UnitSpec2ClFn
{
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator() (const UnitSpec& us) {
    return us.cl();
  }
};

void GlobalSubsumption::perform(Clause* cl, ForwardSimplificationPerformer* simplPerformer)
{
  CALL("GlobalSubsumption::perform/2");

  static Stack<UnitSpec> prems;  
  
  Clause* newCl = perform(cl,prems);
  if(newCl==cl) {
    return;
  }
    
  Stack<UnitSpec>::BottomFirstIterator it(prems);
              
  ALWAYS(simplPerformer->willPerform(0));
  simplPerformer->perform(pvi( getMappingIterator(it, UnitSpec2ClFn()) ), newCl);
  ALWAYS(!simplPerformer->clauseKept());
}

}
