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

#include "SAT/SATLiteral.hpp"
#include "SAT/ISSatSweeping.hpp"
#include "SAT/Preprocess.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/TWLSolver.hpp"

#include "Test/RecordingSatSolver.hpp"

#include "EquivalenceDiscoverer.hpp"
#include "Flattening.hpp"
#include "PDInliner.hpp"
#include "PDUtils.hpp"
#include "Preprocess.hpp"
#include "Property.hpp"

namespace Shell
{

using namespace Kernel;
using namespace SAT;

EquivalenceDiscoverer::EquivalenceDiscoverer(bool normalizeForSAT, unsigned satConflictCountLimit,
    CandidateRestriction restriction, bool discoverImplications, bool doRandomSimulation,
    bool proofTracing)
    : _satConflictCountLimit(satConflictCountLimit),
      _restriction(restriction),
      _discoverImplications(discoverImplications),
      _doRandomSimulation(doRandomSimulation),
      _proofTracing(proofTracing),
      _restrictedRange(false),
      _gnd(normalizeForSAT),
      _maxSatVar(0)
{
  CALL("EquivalenceDiscoverer::EquivalenceDiscoverer");

  _solver = new TWLSolver(*env -> options, false);
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

  SATClause* scl = _gnd.groundNonProp(cl, false, normLits.array());
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
//    if(env -> signature->getPredicate(l->functor())->introduced()) {
//      return false;
//    }
  }
  if(_restriction==CR_EQUIVALENCES && !PDUtils::isDefinitionHead(l)) {
    return false;
  }
  return true;
}

bool EquivalenceDiscoverer::isPredDefinition(Literal* lhs, Literal* rhs)
{
  CALL("EquivalenceDiscoverer::isPredDefinition");

  if(!PDUtils::isDefinitionHead(lhs)) {
    return false;
  }
  if(!lhs->containsAllVariablesOf(rhs)) {
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

  Literal* pl1 = Literal::positiveLiteral(l1);
  Literal* pl2 = Literal::positiveLiteral(l2);

  ASS(isEligible(pl1));
  ASS(isEligible(pl2));

  if(_restrictedRange) {
    if( (!_restrictedRangeSet1.contains(pl1) || !_restrictedRangeSet2.contains(pl2)) &&
        (!_restrictedRangeSet1.contains(pl2) || !_restrictedRangeSet2.contains(pl1)) ) {
      return false;
    }
  }

  switch(_restriction) {
  case CR_EQUIVALENCES:
    //these follow from the restriction in isEligible
    ASS(PDUtils::isDefinitionHead(l1));
    ASS(PDUtils::isDefinitionHead(l2));
    if(!l1->containsAllVariablesOf(l2) || !l2->containsAllVariablesOf(l1)) {
      return false;
    }
    break;
  case CR_DEFINITIONS:
  {
    if(!isPredDefinition(l1, l2) && !isPredDefinition(l2, l1)) {
      return false;
    }
    break;
  }
  case CR_NONE:
    break;
  }

  return true;
}

void EquivalenceDiscoverer::collectRelevantLits()
{
  CALL("EquivalenceDiscoverer::collectRelevantLits");

  DHSet<SATLiteral> seen;

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

      if (env->options->showPreprocessing()) {
        env->beginOutput();
        env->out() << "[PP] ed_lits: fo: "<<(*npLit)<<"  sat: "<<slit.toString() << std::endl;
        env->endOutput();
      }
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

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] groundings added" << std::endl;
    env->endOutput();
  }

  _filteredSatClauses.loadFromIterator(
      SAT::Preprocess::filterPureLiterals(_maxSatVar+1,
	  SAT::Preprocess::removeDuplicateLiterals(pvi(SATClauseStack::Iterator(_satClauses)))));

  collectRelevantLits();

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] relevant literals collected" << std::endl;
    env->endOutput();
  }
  
  _solver->ensureVarCnt(_maxSatVar+1);
  _solver->addClauses(pvi(SATClauseStack::Iterator(_filteredSatClauses)));

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] grounded clauses added to SAT solver" << std::endl;
    env->endOutput();
  }
    
  if(_solver->getStatus()==SATSolver::UNSATISFIABLE) {
    //we might have built a refutation clause here but this is highly unlikely case anyway...
    return 0;
  }
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  //the actual equivalence finding
  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] starting equivalence discovery among "
            <<_eligibleSatLits.size()<<" atoms" << std::endl;
    env->endOutput();
  }
  
  UnitList* res = 0;
  doISSatDiscovery(res);

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] finished" << std::endl;
    env->endOutput();
  }

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

    // a relict of the LOGGING module -- could RecordingSatSolver be still useful?
    /*if(TAG_ENABLED("sat_recorder")) {
      _proofRecordingSolver = new Test::RecordingSatSolver(new TWLSolver(*env->options, true));
    }
    else*/ {
      _proofRecordingSolver = new TWLSolver(*env->options, true);
    }
    _proofRecordingSolver->ensureVarCnt(_maxSatVar+1);
    _proofRecordingSolver->addClauses(pvi(SATClauseStack::Iterator(clauseCopies)), true);
  }
  ASS_NEQ(_proofRecordingSolver->getStatus(), SATSolver::UNSATISFIABLE);
  ASS(!_proofRecordingSolver->hasAssumptions());
  return *_proofRecordingSolver;
}

/**
 * If l1==SATLiteral::dummy(), it is not asserted and
 * we assume that just l2.opposite() is unsatisfiable.
 */
void EquivalenceDiscoverer::getImplicationPremises(SATLiteral l1, SATLiteral l2, Stack<UnitSpec>& acc)
{
  CALL("EquivalenceDiscoverer::getImplicationPremises");
  ASS(l2!=SATLiteral::dummy())

  if(!_proofTracing) {
    //we don't add any premises to the stack
    return;
  }

  SATSolver& ps = getProofRecordingSolver();
  ASS(!ps.hasAssumptions());

  if(l1!=SATLiteral::dummy()) {
    ps.addAssumption(l1,true);
  }
  ps.addAssumption(l2.opposite(),false);
  ASS_EQ(ps.getStatus(), SATSolver::UNSATISFIABLE);
  SATClause* ref = ps.getRefutation();
  SATInference::collectFOPremises(ref, acc);
  ps.retractAllAssumptions();
}

/**
 * If @c equivalence is true, return inference for equivalence l1 <-> l2.
 * If @c equivalence is false and l1==SATLiteral::dummy(), return inference
 * for atom l2.
 * If @c equivalence is false and l1!=SATLiteral::dummy(), return inference
 * for implication l1 -> l2.
 */
Inference* EquivalenceDiscoverer::getInference(SATLiteral l1, SATLiteral l2, bool equivalence)
{
  CALL("EquivalenceDiscoverer::getEquivInference");
  ASS_NEQ(l2,SATLiteral::dummy());
  ASS(!equivalence || l1!=SATLiteral::dummy());

  static Stack<UnitSpec> premises;
  ASS(premises.isEmpty());

  getImplicationPremises(l1, l2, premises);
  if(equivalence) {
    getImplicationPremises(l2, l1, premises);
  }

  UnitList* premLst = 0;

  while(premises.isNonEmpty()) {
    UnitSpec us = premises.pop();
    UnitList::push(us.unit(), premLst);
  }
  return new InferenceMany(Inference::EQUIVALENCE_DISCOVERY, premLst);
}

void EquivalenceDiscoverer::doISSatDiscovery(UnitList*& res)
{
  CALL("EquivalenceDiscoverer::doISSatDiscovery");
  ASS_EQ(_solver->getStatus(),SATSolver::SATISFIABLE);

  ISSatSweeping sswp(_maxSatVar+1, *_solver,
      pvi( getMappingIteratorKnownRes<int>(SATLiteralStack::ConstIterator(_eligibleSatLits), satLiteralVar) ),
      _doRandomSimulation, _satConflictCountLimit, _discoverImplications);

  Stack<ISSatSweeping::Equiv>::ConstIterator eqIt(sswp.getEquivalences());
  while(eqIt.hasNext()) {
    ISSatSweeping::Equiv eq = eqIt.next();
    handleEquivalence(eq.first, eq.second, res);
  }

  SATLiteralStack::ConstIterator tlit(sswp.getTrueLiterals());
  while(tlit.hasNext()) {
    SATLiteral trueLit = tlit.next();
    handleTrueLiteral(trueLit, res);
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

bool EquivalenceDiscoverer::handleTrueLiteral(SATLiteral l, UnitList*& eqAcc)
{
  CALL("EquivalenceDiscoverer::handleTrueLiteral");

  Literal* fl = getFOLit(l);

  if(_restriction==CR_DEFINITIONS) {
    if(!PDUtils::isDefinitionHead(fl)) {
      return false;
    }
  }

  Formula* atomForm = new AtomicFormula(fl);
  Formula::VarList* freeVars = atomForm->freeVariables();
  if(freeVars) {
    atomForm = new QuantifiedFormula(FORALL, freeVars, atomForm);
  }

  Inference* inf = getInference(SATLiteral::dummy(), l, false);
  FormulaUnit* fu = new FormulaUnit(atomForm, inf, Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] ed_tl: " << fu->toString() << std::endl;
    env->endOutput();
  }

  return false;
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

  Inference* inf = getInference(l1, l2, true);
  FormulaUnit* fu = new FormulaUnit(eqForm, inf, Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] ed_eq: " << fu->toString() << std::endl;
    env->endOutput();
  }

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

  Inference* inf = getInference(lhs, rhs, false);
  FormulaUnit* fu = new FormulaUnit(eqForm, inf, Unit::AXIOM);
  UnitList::push(fu, eqAcc);

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "[PP] ed_imp: " << fu->toString() << std::endl;
    env->endOutput();
  }

  return true;
}

UnitList* EquivalenceDiscoverer::getEquivalences(UnitList* units, const Options* opts)
{
  CALL("EquivalenceDiscoverer::getEquivalences");
  ASS(opts);

  Options prepOpts;
  if(opts) { prepOpts = *opts; }
  prepOpts.setPredicateEquivalenceDiscovery(Options::PED_OFF);

  Problem prb(units->copy());

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    env->out() << "--- preprocessing for equivalence discovery started ---" << std::endl;
  }
  Preprocess prepr(prepOpts);
  prepr.preprocess(prb);
  if (env->options->showPreprocessing()) {
    env->out() << "--- preprocessing for equivalence discovery finished ---" << std::endl;
    env->endOutput();
  }
  //TODO: we will leak the results of this preprocessing iteration

  return getEquivalences(prb.clauseIterator());
}


//////////////////////////////////////
// FormulaEquivalenceDiscoverer
//

UnitList* FormulaEquivalenceDiscoverer::getEquivalences(UnitList* units, const Options* opts)
{
  CALL("FormulaEquivalenceDiscoverer::getEquivalences");

  _fresh.use();

  UnitList* namedUnits = units->copy();
  _adi.apply(namedUnits);
  UnitList* foundEquivs = _ed.getEquivalences(namedUnits, opts);

  UnitList* res = collectOuterEquivalences(foundEquivs);

  //TODO: we leak the created units
  namedUnits->destroy();
  foundEquivs->destroy();

  return res;
}

/**
 * Try to convert inner formula to outer, expanding the introduced names.
 *
 * If a particular conversion is not supported, return 0.
 *
 * Now the function converts TRUE, FALSE (as they need no conversion)
 * and LITERALs that either aren't introduced names (and need no conversion),
 * or are the exact literals that were introduced by the naming rule
 * (no instantiation is done).
 */
Formula* FormulaEquivalenceDiscoverer::inner2Outer(Formula* inner, UnitStack& premAcc)
{
  CALL("FormulaEquivalenceDiscoverer::inner2Outer");

  Connective con = inner->connective();

  if(con==TRUE || con==FALSE) {
    return inner;
  }
  if(con!=LITERAL) {
    return 0;
  }

  Literal* lit = inner->literal();
  unsigned pred = lit->functor();


  Unit* prem = 0;
  if(!_adi.introducedPreds().contains(pred)) {
    return inner;
  }
  Formula* res = _adi.getNamedFormula(lit, prem);
  if(!res) {
    //cannot translate the name, so we skip this equivalence
    return 0;
  }
  ASS(prem);
  premAcc.push(prem);
  return res;
}

UnitList* FormulaEquivalenceDiscoverer::collectOuterEquivalences(UnitList* namedEqs)
{
  CALL("FormulaEquivalenceDiscoverer::collectOuterEquivalences");

  static UnitStack prems;

  UnitList* res = 0;
  UnitList::Iterator uit(namedEqs);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS(!u->isClause());
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    Formula* f1;
    Formula* f2;
    Connective con;
    if(!PDUtils::isAtomBinaryFormula(fu, con, f1, f2)) {
      ALWAYS(PDUtils::isUnitAtom(fu, f1));
      f2 = Formula::trueFormula();
      con = IFF;
    }

    prems.reset();
    Formula* f1o = inner2Outer(f1, prems);
    Formula* f2o = inner2Outer(f2, prems);

    if(!f1o || !f2o) {
      //couldn't translate the introduced names, so we skip this equivalence
      if (env->options->showPreprocessing()) {
        env->beginOutput();
        env->out() << "[PP] ed_form_failed: " << u->toString() << std::endl;
        env->endOutput();
      }
      continue;
    }
    if(f1o==f1 && f2o==f2) {
      //no need to translate, we just use the original equivalence
      UnitList::push(u, res);
      if (env->options->showPreprocessing()) {
        env->beginOutput();
        env->out() << "[PP] ed_form_res_direct: " << u->toString() << std::endl;
        env->endOutput();
      }
      continue;
    }
    ASS(prems.isNonEmpty());
    prems.push(u);

    Formula* eqForm;
    if(con==IFF && f2o->connective()==TRUE) {
      //we handle the case of getting an unit atom from the original formula
      eqForm = f1o;
    }
    else {
      eqForm = new BinaryFormula(con, f1o, f2o);
    }
    eqForm = Formula::quantify(eqForm);
    eqForm = Flattening::flatten(eqForm);

    UnitList* premLst = 0;
    UnitList::pushFromIterator(UnitStack::Iterator(prems), premLst);
    Inference* inf = new InferenceMany(Inference::DEFINITION_UNFOLDING, premLst);
    FormulaUnit* newUnit = new FormulaUnit(eqForm, inf, Unit::getInputType(premLst));

    UnitList::push(newUnit,res);
    if (env->options->showPreprocessing()) {
      env->beginOutput();
      env->out() << "[PP] ed_form_res_translated: " << newUnit->toString() << std::endl;
      env->endOutput();
    }    
  }
  return res;
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
    prb.invalidateEverything();
    return true;
  }
  return false;
}

bool EquivalenceDiscoveringTransformer::apply(UnitList*& units)
{
  CALL("EquivalenceDiscoveringTransformer::apply(UnitList*&)");

  bool formulaDiscovery = false;

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
  case Options::PED_ALL_FORMULAS:
    restr = EquivalenceDiscoverer::CR_NONE;
    formulaDiscovery = true;
    break;
  case Options::PED_OFF:
  default:
    ASSERTION_VIOLATION;
  }

  EquivalenceDiscoverer eqd(true, _opts.predicateEquivalenceDiscoverySatConflictLimit(), restr,
      _opts.predicateEquivalenceDiscoveryAddImplications(),
      _opts.predicateEquivalenceDiscoveryRandomSimulation(), true);
  UnitList* equivs;

  if(formulaDiscovery) {
    FormulaEquivalenceDiscoverer fed(eqd);
    equivs = fed.getEquivalences(units, &_opts);
  }
  else {
    equivs = eqd.getEquivalences(units, &_opts);
  }
  if(!equivs) {
    return false;
  }

  units = UnitList::concat(equivs, units);

  PDInliner inl;
  inl.apply(units, true);

  return true;
}



}
