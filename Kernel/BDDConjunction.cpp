/**
 * @file BDDConjunction.cpp
 * Implements class BDDConjunction.
 */

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "SAT/TWLSolver.hpp"

#include "Shell/Options.hpp"

#include "BDD.hpp"
#include "BDDConjunction.hpp"

using namespace Kernel;

/**
 * @since 05/05/2013 references to removed sat solver options removed
 * @author Andrei Voronkov
 */
BDDConjunction::BDDConjunction(const Options& opt)
: _isFalse(false),
  // _clausifier(opt.satSolverWithSubsumptionResolution(), opt.satSolverWithNaming()),
  _clausifier(false,false),
  _solver(new TWLSolver(opt))
{
}


/**
 * Add the formula represented by @b n to the conjunction represented
 * by this object
 */
void BDDConjunction::addNode(BDDNode* n)
{
  CALL("BDDConjunction::addNode");

  if(_isFalse) {
    return;
  }

  BDD* bdd=BDD::instance();

  if(bdd->isConstant(n)) {
    if(bdd->isFalse(n)) {
      _isFalse=true;
    } else {
      ASS(bdd->isTrue(n));
    }
    return;
  }

  static SATClauseStack acc;
  acc.reset();

  {
    TimeCounter tc(TC_BDD_CLAUSIFICATION);
    _clausifier.clausify(n, acc);
  }

  TimeCounter tc(TC_SAT_SOLVER);

  _solver->ensureVarCount(_clausifier.getCNFVarCount());
  _solver->addClausesIter(pvi( SATClauseStack::Iterator(acc) ));

  if(_solver->solve()==SATSolver::UNSATISFIABLE) {
    _isFalse=true;
  }

  return;
}
