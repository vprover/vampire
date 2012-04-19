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

#include "SAT/ISSatSweeping.hpp"
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
    CandidateRestriction restriction, bool discoverImplications)
    : _satConflictCountLimit(satConflictCountLimit),
      _restriction(restriction),
      _discoverImplications(discoverImplications),
      _restrictedRange(false),
      _gnd(normalizeForSAT),
      _maxSatVar(0)
{
  CALL("EquivalenceDiscoverer::EquivalenceDiscoverer");

  _solver = new TWLSolver(*env.options, false);
}

/**
 * Restrict equivalence discovery only to equivalences between elements of @c set1 and @c set2.
 */
void EquivalenceDiscoverer::setRestrictedRange(LiteralIterator set1, LiteralIterator set2)
{
  CALL("EquivalenceDiscoverer::setRestrictedRange");

  _restrictedRange = true;
  _restrictedRangeSet1.loadFromIterator(getMappingIteratorKnownRes<Literal*>(set1, Literal::positiveLiteral));
  _restrictedRangeSet2.loadFromIterator(getMappingIteratorKnownRes<Literal*>(set2, Literal::positiveLiteral));
}

void EquivalenceDiscoverer::addGrounding(Clause* cl)
{
  CALL("EquivalenceDiscoverer::addGrounding");

  unsigned clen = cl->length();
  static DArray<Literal*> normLits;
  normLits.ensure(clen);

  SATClause* scl = _gnd.groundNonProp(cl, normLits.array());
  scl->setInference(new FOConversionInference(cl));
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

  if(_restrictedRange) {
    if(!_restrictedRangeSet1.contains(l) && !_restrictedRangeSet2.contains(l)) {
      return false;
    }
  }
  else {
//    if(env.signature->getPredicate(l->functor())->introduced()) {
//      return false;
//    }
  }
  if(_restriction==CR_EQUIVALENCES && !PDUtils::isDefinitionHead(l)) {
    return false;
  }
  return true;
}

/**
 * Return true if equivalence or implication between l1 and l2 can be
 * added to the problem.
 *
 * Literals l1 and l2 on its own must already be eligible for processing
 * (isEligible gives true).
 */
bool EquivalenceDiscoverer::isEligiblePair(Literal* l1, Literal* l2)
{
  CALL("EquivalenceDiscoverer::isEligiblePair");
  ASS(isEligible(l1));
  ASS(isEligible(l2));

  if(_restrictedRange) {
    if( (!_restrictedRangeSet1.contains(l1) || !_restrictedRangeSet2.contains(l2)) &&
        (!_restrictedRangeSet1.contains(l2) || !_restrictedRangeSet2.contains(l1)) ) {
      return false;
    }
  }

  switch(_restriction) {
  case CR_EQUIVALENCES:
    //these follow from the restriction in isEligible
    ASS(PDUtils::isDefinitionHead(l1));
    ASS(PDUtils::isDefinitionHead(l2));
    break;
  case CR_DEFINITIONS:
    if(!PDUtils::isDefinitionHead(l1) && !PDUtils::isDefinitionHead(l2)) {
      return false;
    }
    break;
  case CR_NONE:
    break;
  }

  return true;
}

void EquivalenceDiscoverer::collectRelevantLits()
{
  CALL("EquivalenceDiscoverer::collectRelevantLits");

  DHSet<SATLiteral> seen;

  Stack<SATLiteral> nonTrivialPosLits;

  SATClauseStack::ConstIterator scit(_filteredSatClauses);
  while(scit.hasNext()) {
    SATClause* sc = scit.next();
    SATClause::Iterator slitIt(*sc);
    while(slitIt.hasNext()) {
      SATLiteral slit = slitIt.next();

      if(slit.isNegative()) {
	//we can skip negative literals, because we removed trivial variables,
	//so for each negative literal we'll encounter also a positive one with
	//the same variable
	continue;
      }

      if(!seen.insert(slit)) { continue; }

      //positive polarity of the SAT literal should be in the s2f map because we have
      //removed all pure literals before calling this function in the getEquivalences()
      Literal* npLit = _s2f.get(slit);

      if(!isEligible(npLit)) { continue; }

      _eligibleSatLits.push(slit);
    }
  }
}

UnitList* EquivalenceDiscoverer::getEquivalences(ClauseIterator clauses)
{
  CALL("EquivalenceDiscoverer::getEquivalences");

  //we can call getEquivalences only onse per object
  _fresh.use();

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
  _solver->addClauses(pvi(SATClauseStack::Iterator(_filteredSatClauses)));

  LOG("pp_ed_progress","grounded clauses added to SAT solver");

  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    //we might have built a refutation clause here but this is highly unlikely case anyway...
    return 0;
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  //the actual equivalence finding

  LOG("pp_ed_progress","starting equivalence discovery among "<<_eligibleSatLits.size()<<" atoms");

  UnitList* res = 0;
  doISSatDiscovery(res);

  LOG("pp_ed_progress","finished");

  return res;
}

SATSolver& EquivalenceDiscoverer::getProofRecordingSolver()
{
  CALL("EquivalenceDiscoverer::getProofRecordingSolver");

  if(!_proofRecordingSolver) {

    //we need to make copies of clauses as the same clause object
    //cannot be in two SAT solver objects at once (SAT solvers can modify clauses)

    SATClauseStack clauseCopies;
    SATClauseStack::Iterator cit(_filteredSatClauses);
    while(cit.hasNext()) {
      SATClause* cl = cit.next();
      SATClause* clCopy = SATClause::copy(cl);
      clauseCopies.push(clCopy);
    }

    _proofRecordingSolver = new TWLSolver(*env.options, true);
    _proofRecordingSolver->ensureVarCnt(_maxSatVar+1);
    _proofRecordingSolver->addClauses(pvi(SATClauseStack::Iterator(clauseCopies)), true);
  }
  ASS_NEQ(_proofRecordingSolver->getStatus(), SATSolver::UNSATISFIABLE);
  ASS(!_proofRecordingSolver->hasAssumptions());
  return *_proofRecordingSolver;
}

void EquivalenceDiscoverer::getImplicationPremises(SATLiteral l1, SATLiteral l2, Stack<UnitSpec>& acc)
{
  CALL("EquivalenceDiscoverer::getImplicationPremises");

  SATSolver& ps = getProofRecordingSolver();
  ASS(!ps.hasAssumptions());

  ps.addAssumption(l1,true);
  ps.addAssumption(l2.opposite(),false);
  ASS_EQ(ps.getStatus(), SATSolver::UNSATISFIABLE);
  SATClause* ref = ps.getRefutation();
  SATInference::collectFOPremises(ref, acc);
  ps.retractAllAssumptions();
}

/**
 * If @c implication is true, return inference for implication l1 -> l2,
 * otherwise return inference for equivalence l1 <-> l2.
 */
Inference* EquivalenceDiscoverer::getInference(SATLiteral l1, SATLiteral l2, bool implication)
{
  CALL("EquivalenceDiscoverer::getEquivInference");

  static Stack<UnitSpec> premises;
  ASS(premises.isEmpty());

  getImplicationPremises(l1, l2, premises);
  if(!implication) {
    getImplicationPremises(l2, l1, premises);
  }

  UnitList* premLst = 0;

  while(premises.isNonEmpty()) {
    UnitSpec us = premises.pop();
    ASS(us.withoutProp());
    UnitList::push(us.unit(), premLst);
  }
  return new InferenceMany(Inference::EQUIVALENCE_DISCOVERY, premLst);
}

void EquivalenceDiscoverer::doISSatDiscovery(UnitList*& res)
{
  CALL("EquivalenceDiscoverer::doISSatDiscovery");
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  ISSatSweeping sswp(_maxSatVar+1, *_solver,
      pvi( getMappingIteratorKnownRes<int>(SATLiteralStack::ConstIterator(_eligibleSatLits), satLiteralVar) ));

  Stack<ISSatSweeping::Equiv>::ConstIterator eqIt(sswp.getEquivalences());
  while(eqIt.hasNext()) {
    ISSatSweeping::Equiv eq = eqIt.next();
    handleEquivalence(eq.first, eq.second, res);
  }
  //TODO: make better equivalence retrieval for CR_DEFINITIONS

  if(_discoverImplications) {
    const IntUnionFind& eqClasses = sswp.getEquivalenceClasses();
    DHSet<ISSatSweeping::Impl>::Iterator implIt(sswp.getImplications());
    while(implIt.hasNext()) {
      ISSatSweeping::Impl impl = implIt.next();
      unsigned v1 = impl.first.var();
      unsigned v2 = impl.second.var();
      if(eqClasses.root(v1)==eqClasses.root(v2)) {
	//this implication is subsumed by some equivalence
	continue;
      }
      handleImplication(impl.first, impl.second, res);
    }
  }
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

  if(!isEligiblePair(fl1, fl2)) {
    return false;
  }

  Formula* eqForm = new BinaryFormula(IFF, new AtomicFormula(fl1), new AtomicFormula(fl2));
  Formula::VarList* freeVars = eqForm->freeVariables();
  if(freeVars) {
    eqForm = new QuantifiedFormula(FORALL, freeVars, eqForm);
  }

  Inference* inf = getInference(l1, l2, false);
  FormulaUnit* fu = new FormulaUnit(eqForm, inf, Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  LOG_UNIT("pp_ed_eq",fu);
  TRACE("pp_ed_eq_prems",
	UnitSpecIterator uit = InferenceStore::instance()->getParents(UnitSpec(fu));
	while(uit.hasNext()) {
	  UnitSpec p = uit.next();
	  TRACE_OUTPUT_UNIT(p.unit());
	}
  );

  return true;
}

/**
 * If possible and eligible, add FO version of implication lhs -> rhs into @c eqAcc.
 */
bool EquivalenceDiscoverer::handleImplication(SATLiteral lhs, SATLiteral rhs, UnitList*& eqAcc)
{
  CALL("EquivalenceDiscoverer::handleImplication");
  ASS_NEQ(lhs.var(), rhs.var());

  Literal* flhs = getFOLit(lhs);
  Literal* frhs = getFOLit(rhs);

  static DHMap<unsigned,unsigned> varSorts;
  varSorts.reset();
  if(!SortHelper::areSortsValid(flhs, varSorts) || !SortHelper::areSortsValid(frhs, varSorts)) {
    return false;
  }

  if(!isEligiblePair(flhs, frhs)) {
    return false;
  }

  Formula* eqForm = new BinaryFormula(IMP, new AtomicFormula(flhs), new AtomicFormula(frhs));
  Formula::VarList* freeVars = eqForm->freeVariables();
  if(freeVars) {
    eqForm = new QuantifiedFormula(FORALL, freeVars, eqForm);
  }

  Inference* inf = getInference(lhs, rhs, true);
  FormulaUnit* fu = new FormulaUnit(eqForm, inf, Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  LOG_UNIT("pp_ed_imp",fu);
  TRACE("pp_ed_imp_prems",
	UnitSpecIterator uit = InferenceStore::instance()->getParents(UnitSpec(fu));
	while(uit.hasNext()) {
	  UnitSpec p = uit.next();
	  TRACE_OUTPUT_UNIT(p.unit());
	}
  );

  return true;
}

UnitList* EquivalenceDiscoverer::getEquivalences(UnitList* units, const Options* opts)
{
  CALL("EquivalenceDiscoverer::getEquivalences");

  Options prepOpts;
  if(opts) { prepOpts = *opts; }
  prepOpts.setPredicateEquivalenceDiscovery(Options::PED_OFF);

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

  EquivalenceDiscoverer::CandidateRestriction restr;
  switch(_opts.predicateEquivalenceDiscovery()) {
  case Options::PED_ALL_ATOMS:
    restr = EquivalenceDiscoverer::CR_NONE;
    break;
  case Options::PED_DEFINITIONS:
    restr = EquivalenceDiscoverer::CR_DEFINITIONS;
    break;
  case Options::PED_ON:
    restr = EquivalenceDiscoverer::CR_EQUIVALENCES;
    break;
  case Options::PED_OFF:
  default:
    ASSERTION_VIOLATION;
  }

  EquivalenceDiscoverer eqd(true, _opts.predicateEquivalenceDiscoverySatConflictLimit(), restr,
      _opts.predicateEquivalenceDiscoveryAddImplications());
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
