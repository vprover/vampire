/**
 * @file BDDConjunction.cpp
 * Implements class BDDConjunction.
 */

#include "../Lib/TimeCounter.hpp"

#include "BDD.hpp"

#include "BDDConjunction.hpp"

namespace Kernel
{

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

  _solver.ensureVarCnt(_clausifier.getCNFVarCount());
  _solver.addClauses(pvi( SATClauseStack::Iterator(acc) ));

  if(_solver.getStatus()==TWLSolver::UNSATISFIABLE) {
    _isFalse=true;
  }

  return;
}

}
