/**
 * @file EquivalenceDiscoverer.cpp
 * Implements class EquivalenceDiscoverer.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Grounder.hpp"
#include "Kernel/Term.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/TWLSolver.hpp"

#include "EquivalenceDiscoverer.hpp"
#include "PDUtils.hpp"

namespace Shell
{

using namespace Kernel;
using namespace SAT;

EquivalenceDiscoverer::EquivalenceDiscoverer(bool normalizeForSAT, bool onlyPropEqCheck)
    : _onlyPropEqCheck(onlyPropEqCheck), _gnd(normalizeForSAT), _maxSatVar(0)
{
  _solver = new TWLSolver(*env.options, true);
}

void EquivalenceDiscoverer::addGrounding(Clause* cl)
{
  CALL("EquivalenceDiscoverer::addGrounding");

  unsigned clen = cl->length();
  static DArray<Literal*> normLits;
  normLits.ensure(clen);

  SATClause* scl = _gnd.groundNonProp(cl, normLits.array());
  _satClauses.push(scl);

  for(unsigned i=0; i<clen; ++i) {
    Literal* nlit = normLits[i];
    SATLiteral slit = (*scl)[i];

    if(slit.var()>_maxSatVar) {
      _maxSatVar = slit.var();
    }

    _s2f.insert(slit, nlit);
  }
}

/**
 * Return true if literal @c l is eligible for equivalence discovery
 *
 * (we will attempt to discover equivalences between pairs of eligible literals)
 */
bool EquivalenceDiscoverer::isEligible(Literal* l)
{
  CALL("EquivalenceDiscoverer::isEligible");

//  return PDUtils::isDefinitionHead(l);
  return PDUtils::isDefinitionHead(l) && !env.signature->getPredicate(l->functor())->introduced();
}

void EquivalenceDiscoverer::collectRelevantLits()
{
  CALL("EquivalenceDiscoverer::collectRelevantLits");

  DHSet<SATLiteral> seen;

  SATClauseStack::Iterator scit(_filteredSatClauses);
  while(scit.hasNext()) {
    SATClause* sc = scit.next();
    SATClause::Iterator slitIt(*sc);
    while(slitIt.hasNext()) {
      SATLiteral slit = slitIt.next();

      SATLiteral spLit = slit.isPositive() ? slit : slit.opposite();
      if(!seen.insert(spLit)) { continue; }

      //positive polarity of the SAT literal should be in the s2f map because we have
      //removed all pure literals before calling this function in the getEquivalences()
      Literal* npLit = _s2f.get(spLit);

      if(!isEligible(npLit)) { continue; }

      _eligibleSatLits.push(spLit);
    }
  }
}

UnitList* EquivalenceDiscoverer::getEquivalences(ClauseIterator clauses)
{
  CALL("EquivalenceDiscoverer::getEquivalences");

  DArray<Literal*> norm;
  while(clauses.hasNext()) {
    Clause* cl = clauses.next();
    addGrounding(cl);
  }

  LOG("pp_ed_progress","groundings added");

  _filteredSatClauses.loadFromIterator(
      SAT::Preprocess::filterPureLiterals(_maxSatVar+1,
	  SAT::Preprocess::removeDuplicateLiterals(pvi(SATClauseStack::Iterator(_satClauses)))));

  collectRelevantLits();

  LOG("pp_ed_progress","relevant literals collected");

  _solver->ensureVarCnt(_maxSatVar+1);
  _solver->addClauses(pvi(SATClauseStack::Iterator(_filteredSatClauses)), true);

  LOG("pp_ed_progress","grounded clauses added to SAT solver");

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    //we might have built a refutation clause here but this is highly unlikely case anyway...
    return 0;
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  //the actual equivalence finding

  UnitList* res = 0;

  unsigned elCnt = _eligibleSatLits.size();
  for(unsigned i=0; i<elCnt; ++i) {
    SATLiteral l1 = _eligibleSatLits[i];
    for(unsigned j=i+1; j<elCnt; ++j) {
      SATLiteral l2 = _eligibleSatLits[j];
      ASS_NEQ(l1,l2);
      if(areEquivalent(l1,l2)) {
	handleEquivalence(l1, l2, res);
	break;
      }
    }
  }
  LOG("pp_ed_progress","finished");

  return res;
}

void EquivalenceDiscoverer::handleEquivalence(SATLiteral l1, SATLiteral l2, UnitList*& eqAcc)
{
  CALL("EquivalenceDiscoverer::handleEquivalence");

  ASS_NEQ(l1.var(), l2.var());

  static SATLiteralStack slits;
  slits.reset();
  slits.push(l1);
  slits.push(l2.opposite());
  SATClause* scl1 = SATClause::fromStack(slits);

  slits.reset();
  slits.push(l1.opposite());
  slits.push(l2);
  SATClause* scl2 = SATClause::fromStack(slits);

  _solver->addClauses(
      pvi( getConcatenatedIterator(getSingletonIterator(scl1),getSingletonIterator(scl2)) ));

  Literal* fl1 = _s2f.get(l1);
  Literal* fl2 = _s2f.get(l2);

  Formula* eqForm = new BinaryFormula(IFF, new AtomicFormula(fl1), new AtomicFormula(fl2));
  //TODO: proof tracking
  FormulaUnit* fu = new FormulaUnit(eqForm, new Inference(Inference::EQUIVALENCE_DISCOVERY), Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  LOG_UNIT("pp_ed_eq",fu);
}

bool EquivalenceDiscoverer::areEquivalent(SATLiteral l1, SATLiteral l2)
{
  CALL("EquivalenceDiscoverer::areEquivalent");
  ASS_NEQ(l1,l2);
  ASS(!_solver->hasAssumptions());
  ASS_NEQ(_solver->getStatus(),SATSolver::UNSATISFIABLE);

  bool firstAssumptionPropOnly = true;
//  bool firstAssumptionPropOnly = _onlyPropEqCheck;

  LOG("pp_ed_asm","asserted l1: "<<l1);
  _solver->addAssumption(l1, firstAssumptionPropOnly);
  LOG("pp_ed_asm","result for l1: "<<_solver->getStatus());
  LOG("pp_ed_asm","asserted ~l2: "<<l2.opposite());
  _solver->addAssumption(l2.opposite(), _onlyPropEqCheck);

  SATSolver::Status status = _solver->getStatus();
  LOG("pp_ed_asm","result for ~(l1=>l2): "<<status);
  _solver->retractAllAssumptions();
  LOG("pp_ed_asm","assumptions retracted");

  if(status!=SATSolver::UNSATISFIABLE) {
    return false;
  }
  LOG("pp_ed_asm","asserted ~l1: "<<l1.opposite());
  _solver->addAssumption(l1.opposite(), firstAssumptionPropOnly);
  LOG("pp_ed_asm","result for ~l1: "<<_solver->getStatus());
  LOG("pp_ed_asm","asserted l2: "<<l2);
  _solver->addAssumption(l2, _onlyPropEqCheck);

  status = _solver->getStatus();
  LOG("pp_ed_asm","result for ~(l2=>l1): "<<status);
  _solver->retractAllAssumptions();
  LOG("pp_ed_asm","assumptions retracted");

  return status==SATSolver::UNSATISFIABLE;
}

}
