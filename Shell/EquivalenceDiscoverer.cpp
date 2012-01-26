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
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "SAT/Preprocess.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/TWLSolver.hpp"

#include "EquivalenceDiscoverer.hpp"
#include "PDInliner.hpp"
#include "PDUtils.hpp"
#include "Preprocess.hpp"

namespace Shell
{

using namespace Kernel;
using namespace SAT;

EquivalenceDiscoverer::EquivalenceDiscoverer(bool normalizeForSAT, unsigned satConflictCountLimit,
    bool checkOnlyDefinitionHeads)
    : _satConflictCountLimit(satConflictCountLimit),
      _checkOnlyDefinitionHeads(checkOnlyDefinitionHeads),
      _gnd(normalizeForSAT),
      _maxSatVar(0)
{
  CALL("EquivalenceDiscoverer::EquivalenceDiscoverer");
  _solver = new TWLSolver(*env.options, true);
}

EquivalenceDiscoverer::~EquivalenceDiscoverer()
{
  CALL("EquivalenceDiscoverer::~EquivalenceDiscoverer");
  delete _solver;
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

  if(env.signature->getPredicate(l->functor())->introduced()) {
    return false;
  }

  return !_checkOnlyDefinitionHeads || PDUtils::isDefinitionHead(l);
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

void EquivalenceDiscoverer::loadInitialAssignment()
{
  CALL("EquivalenceDiscoverer::loadInitialAssignment");

  _initialAssignment.ensure(_maxSatVar+1);
  for(unsigned i=1; i<=_maxSatVar; i++) {
    SATSolver::VarAssignment asgn = _solver->getAssignment(i);
    switch(asgn) {
    case SATSolver::DONT_CARE:
      break;
    case SATSolver::FALSE:
    case SATSolver::TRUE:
      _initialAssignment.insert(i, asgn==SATSolver::TRUE);
      break;
    case SATSolver::NOT_KNOWN:
    default:
      ASSERTION_VIOLATION;
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
  _solver->addClauses(pvi(SATClauseStack::Iterator(_filteredSatClauses)), false);

  LOG("pp_ed_progress","grounded clauses added to SAT solver");

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    //we might have built a refutation clause here but this is highly unlikely case anyway...
    return 0;
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  loadInitialAssignment();

  //the actual equivalence finding

  UnitList* res = 0;

  unsigned elCnt = _eligibleSatLits.size();
  LOG("pp_ed_progress","literals to process: "<<elCnt);
  for(unsigned i=0; i<elCnt; ++i) {
    SATLiteral l1 = _eligibleSatLits[i];
    LOG("pp_ed_progress","processing literal "<<(*getFOLit(l1)));
    for(unsigned j=i+1; j<elCnt; ++j) {
      SATLiteral l2 = _eligibleSatLits[j];
      ASS_NEQ(l1,l2);
      if(areEquivalent(l1,l2) && handleEquivalence(l1, l2, res)) {
	break;
      }
      if(areEquivalent(l1,l2.opposite()) && handleEquivalence(l1, l2.opposite(), res)) {
	break;
      }
    }
  }
  LOG("pp_ed_progress","finished");

  return res;
}

Literal* EquivalenceDiscoverer::getFOLit(SATLiteral slit) const
{
  CALL("EquivalenceDiscoverer::getFOLit");

  Literal* res;
  if(_s2f.find(slit, res)) {
    return res;
  }
  res = Literal::complementaryLiteral(_s2f.get(slit.opposite()));
  return res;
}

bool EquivalenceDiscoverer::handleEquivalence(SATLiteral l1, SATLiteral l2, UnitList*& eqAcc)
{
  CALL("EquivalenceDiscoverer::handleEquivalence");

  ASS_NEQ(l1.var(), l2.var());

  Literal* fl1 = getFOLit(l1);
  Literal* fl2 = getFOLit(l2);

  static DHMap<unsigned,unsigned> varSorts;
  varSorts.reset();
  if(!SortHelper::areSortsValid(fl1, varSorts) || !SortHelper::areSortsValid(fl2, varSorts)) {
    return false;
  }

  Formula* eqForm = new BinaryFormula(IFF, new AtomicFormula(fl1), new AtomicFormula(fl2));
  Formula::VarList* freeVars = eqForm->freeVariables();
  if(freeVars) {
    eqForm = new QuantifiedFormula(FORALL, freeVars, eqForm);
  }
  //TODO: proof tracking
  FormulaUnit* fu = new FormulaUnit(eqForm, new Inference(Inference::EQUIVALENCE_DISCOVERY), Unit::AXIOM);
  UnitList::push(fu, eqAcc);


  static SATLiteralStack slits;
  slits.reset();
  slits.push(l1);
  slits.push(l2.opposite());
  SATClause* scl1 = SATClause::fromStack(slits);
  scl1->setInference(new FOConversionInference(UnitSpec(fu)));

  slits.reset();
  slits.push(l1.opposite());
  slits.push(l2);
  SATClause* scl2 = SATClause::fromStack(slits);
  scl2->setInference(new FOConversionInference(UnitSpec(fu)));

  _solver->addClauses(
      pvi( getConcatenatedIterator(getSingletonIterator(scl1),getSingletonIterator(scl2)) ), true);


  LOG_UNIT("pp_ed_eq",fu);
  return true;
}

bool EquivalenceDiscoverer::areEquivalent(SATLiteral l1, SATLiteral l2)
{
  CALL("EquivalenceDiscoverer::areEquivalent");
  ASS_NEQ(l1,l2);
  ASS(!_solver->hasAssumptions());
  ASS_NEQ(_solver->getStatus(),SATSolver::UNSATISFIABLE);

  unsigned v1 = l1.var();
  unsigned v2 = l2.var();
  bool eqPol = l1.polarity()==l2.polarity();

  bool v1InitAsgn;
  bool v2InitAsgn;
  if(!_initialAssignment.find(v1, v1InitAsgn) || !_initialAssignment.find(v2, v2InitAsgn)) {
    return false;
  }
  if((v1InitAsgn==v2InitAsgn)!=eqPol) {
    return false;
  }

  bool firstAssumptionPropOnly = true;
//  bool firstAssumptionPropOnly = _onlyPropEqCheck;

  LOG("pp_ed_asm","asserted l1: "<<l1);
  _solver->addAssumption(l1, firstAssumptionPropOnly);
  LOG("pp_ed_asm","result for l1: "<<_solver->getStatus());
  LOG("pp_ed_asm","asserted ~l2: "<<l2.opposite());
  _solver->addAssumption(l2.opposite(), _satConflictCountLimit);

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
  _solver->addAssumption(l2, _satConflictCountLimit);

  status = _solver->getStatus();
  LOG("pp_ed_asm","result for ~(l2=>l1): "<<status);
  _solver->retractAllAssumptions();
  LOG("pp_ed_asm","assumptions retracted");

  return status==SATSolver::UNSATISFIABLE;
}

UnitList* EquivalenceDiscoverer::getEquivalences(UnitList* units, const Options* opts)
{
  CALL("EquivalenceDiscoverer::getEquivalences");

  Options prepOpts;
  if(opts) { prepOpts = *opts; }
  prepOpts.setPredicateEquivalenceDiscovery(false);

  Problem prb(units->copy());

  Preprocess prepr(prepOpts);
  prepr.preprocess(prb);
  //TODO: we will leak the results of this preprocessing iteration

  return getEquivalences(prb.clauseIterator());
}

//////////////////////////////////////
// EquivalenceDiscoveringTransformer
//

EquivalenceDiscoveringTransformer::EquivalenceDiscoveringTransformer(const Options& opts)
 : _opts(opts)
{

}

bool EquivalenceDiscoveringTransformer::apply(Problem& prb)
{
  CALL("EquivalenceDiscoveringTransformer::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateProperty();
    return true;
  }
  return false;
}

bool EquivalenceDiscoveringTransformer::apply(UnitList*& units)
{
  CALL("EquivalenceDiscoveringTransformer::apply(UnitList*&)");

  EquivalenceDiscoverer eqd(true, _opts.predicateEquivalenceDiscoverySatConflictLimit(), !_opts.predicateEquivalenceDiscoveryAllAtoms());
  UnitList* equivs = eqd.getEquivalences(units, &_opts);
  if(!equivs) {
    return false;
  }

  units = UnitList::concat(equivs, units);

  PDInliner inl;
  inl.apply(units, true);
  return true;
}



}
