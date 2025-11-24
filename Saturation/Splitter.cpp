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
 * @file Splitter.cpp
 * Implements class Splitter.
 */

#include "Splitter.hpp"

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/MainLoop.hpp"

#include "Shell/AnswerLiteralManager.hpp"
#include "Shell/PartialRedundancyHandler.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Shuffling.hpp"

#include "SAT/SATInference.hpp"
#include "SAT/MinimizingSolver.hpp"
#include "SAT/FallbackSolverWrapper.hpp"
#include "SAT/CadicalInterfacing.hpp"
#include "SAT/MinisatInterfacing.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "DP/ShortConflictMetaDP.hpp"
#include "DP/SimpleCongruenceClosure.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation
{

using namespace std;
using namespace Lib;
using namespace Kernel;

void SATClauseExtra::output(std::ostream &out) const {
  out << "sat_clause_recorded";
}

void SplitDefinitionExtra::output(std::ostream &out) const {
  out << component->number();
}

/////////////////////////////
// SplittingBranchSelector
//

void SplittingBranchSelector::init()
{
  _literalPolarityAdvice = _parent.getOptions().splittingLiteralPolarityAdvice();

  SATSolver *inner;
  switch(_parent.getOptions().satSolver()){
    case Options::SatSolver::MINISAT:
      inner = new MinisatInterfacing;
      break;
    case Options::SatSolver::CADICAL:
      inner = new CadicalInterfacing;
      break;
#if VZ3
    case Options::SatSolver::Z3:
      {
        inner = new Z3Interfacing(_parent.getOptions(),_parent.satNaming(), /* unsat core */ false, _parent.getOptions().exportAvatarProblem(), _parent.getOptions().problemExportSyntax());
        if(_parent.getOptions().satFallbackForSMT()){
          // TODO make fallback minimizing?
          SATSolver* fallback = new MinisatInterfacing;
          inner = new FallbackSolverWrapper(inner, fallback);
        }
      }
      break;
#endif
    default:
      ASSERTION_VIOLATION_REP(_parent.getOptions().satSolver());
  }

  if (_parent.getOptions().splittingMinimizeModel()) {
    inner = new MinimizingSolver(inner);
  }

  if(_parent.getOptions().splittingCongruenceClosure()) {
    _dp = new ShortConflictMetaDP(
      new DP::SimpleCongruenceClosure(&_parent.getOrdering()), _parent.satNaming(), *inner);
  }

  ::new(&_solver) ProofProducingSATSolver(inner);
}

void SplittingBranchSelector::updateVarCnt()
{
  unsigned satVarCnt = _parent.maxSatVar();
  unsigned splitLvlCnt = _parent.splitLevelCnt();

  // index by var, but ignore slot 0
  _selected.expand(splitLvlCnt+1);

  // solver may be doing the same, but only internally
  _solver.ensureVarCount(satVarCnt);
}

/**
 * The solver should consider making @b lit false by default.
 */
void SplittingBranchSelector::considerPolarityAdvice(SATLiteral lit)
{
  switch (_literalPolarityAdvice) {
    case Options::SplittingLiteralPolarityAdvice::FALSE:
      _solver.suggestPolarity(lit.var(),!lit.positive());
    break;
    case Options::SplittingLiteralPolarityAdvice::TRUE:
      _solver.suggestPolarity(lit.var(), lit.positive());
    break;
    case Options::SplittingLiteralPolarityAdvice::NONE:
      // do nothing
    break;
    case Options::SplittingLiteralPolarityAdvice::RANDOM:
      _solver.suggestPolarity(lit.var(),Random::getBit());
    break;
    default:
      ASSERTION_VIOLATION;
  }
}

static Color colorFromPossiblyDeepFOConversion(SATClause* scl,Unit*& u)
{
  /* all the clauses added to AVATAR are FO_CONVERSIONs except when there is a duplicate literal
   and SATClause::removeDuplicateLiterals creates an extra inference with a single premise ``in between''.*/
  if (scl->inference()->getType() != SATInference::FO_CONVERSION) {
    ASS_EQ(scl->inference()->getType(),SATInference::PROP_INF);
    PropInference* inf = static_cast<PropInference*>(scl->inference());
    SATClauseList* premises = inf->getPremises();
    ASS_EQ(SATClauseList::length(premises),1);
    scl = premises->head();
  }

  SATInference* inf = scl->inference();

  ASS_EQ(inf->getType(),SATInference::FO_CONVERSION);
  u = static_cast<FOConversionInference*>(inf)->getOrigin();
  const Inference& i = u->inference();
  Inference::Iterator it = i.iterator();
  ASS(i.hasNext(it));
  Unit* u1 = i.next(it);
  ASS(u1->isClause());
  Clause* cl = u1->asClause();
  return cl->color();
}

void SplittingBranchSelector::handleSatRefutation()
{
  SATClause *proof = nullptr;
  SATClauseList *satPremises = nullptr;
#if VZ3
  if(_parent.hasSMTSolver)
    satPremises = _solver.premiseList();
#endif
  if(!satPremises) {
    proof = _solver.proof();
    SATInference::visitFOConversions(proof, [&](SATClause *cl) {
      SATClauseList::push(cl, satPremises);
    });
  }
  ASS(satPremises)

  UnitList *foPremises = nullptr;
  for(auto satPrem : iterTraits(satPremises->iter()))
    UnitList::push(satPrem->inference()->foConversion()->getOrigin(), foPremises);
  ASS(foPremises)

  if (!env.colorUsed) { // color oblivious, simple approach
    Clause *foRef = Clause::empty(
#if VZ3
      _parent.hasSMTSolver
      ? NonspecificInferenceMany(InferenceRule::AVATAR_REFUTATION_SMT, foPremises)
      :
#endif
      Inference(InferenceOfASatClause(InferenceRule::AVATAR_REFUTATION, proof, foPremises))
    );

    // TODO: in principle, the user might be interested in this final clause's age (currently left 0)
    throw MainLoop::RefutationFoundException(foRef);
  } else { // we must produce a well colored proof
    // decide which side is "bigger" and should go "first"
    int colorCnts[3] = {0,0,0};
    SATClauseList::Iterator it1(satPremises);
    while (it1.hasNext()) {
      SATClause* scl = it1.next();
      // cout << "SAT: " << scl->toString() << endl;

      Unit* dummy;
      Color c = colorFromPossiblyDeepFOConversion(scl,dummy);

      ASS_L(c,COLOR_INVALID);
      colorCnts[c]++;
    }

    //cout << colorCnts[0] << " " << colorCnts[1] <<  " " << colorCnts[2] << endl;
    Color sndCol = COLOR_RIGHT;
    if (colorCnts[COLOR_LEFT] < colorCnts[COLOR_RIGHT]) {
      sndCol = COLOR_LEFT;
    }

    // split into first and second
    SATClauseStack first;
    UnitList* first_prems = UnitList::empty();
    SATClauseStack second;
    UnitList* second_prems = UnitList::empty();

    SATClauseList::Iterator it2(satPremises);
    while (it2.hasNext()) {
      SATClause* scl = it2.next();
      Unit* u;
      Color c = colorFromPossiblyDeepFOConversion(scl,u);

      if (c == sndCol) {
        second.push(scl);
        UnitList::push(u,second_prems);
      } else {
        first.push(scl); // contains first col ones and transparent ones together
        UnitList::push(u,first_prems);
      }
    }

    if (colorCnts[sndCol] == 0) { // this is a degenerate case, in which we don't need to interpolate at all
      Inference foInf = NonspecificInferenceMany(InferenceRule::AVATAR_REFUTATION, first_prems);
      Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), foInf);
      throw MainLoop::RefutationFoundException(foRef);
    }

    SATClauseStack result;
    MinisatInterfacing<>::interpolateViaAssumptions(_parent.maxSatVar(),first,second,result);

    // turn result into Formula wrapping its CNF structure
    Formula* interpolant;
    {
      FormulaList* conjuncts = FormulaList::empty();
      unsigned conj_cnt = 0;

      SATClauseStack::Iterator it(result);
      while(it.hasNext()) {
        SATClause* cl = it.next();
        FormulaList* disjuncts = FormulaList::empty();

        for (unsigned i = 0; i < cl->size(); i++) {
          SATLiteral lit = (*cl)[i];

          // get the first order clause
          bool negated = false;
          SplitLevel lvl = _parent.getNameFromLiteralUnsafe(lit);
          if (_parent._db[lvl] == 0) {
            negated = true;
            lvl = _parent.getNameFromLiteralUnsafe(lit.opposite());
            ASS_NEQ(_parent._db[lvl],0);
          }
          Formula* litFla = Formula::fromClause(_parent._db[lvl]->component);
          if (negated) {
            litFla = new NegatedFormula(litFla);
          }
          FormulaList::push(litFla,disjuncts);
        }
        Formula* clFla;
        if (cl->size() == 1) {
          clFla = disjuncts->head();
          FormulaList::destroy(disjuncts);
        } else {
          clFla = JunctionFormula::generalJunction(OR, disjuncts);
        }
        FormulaList::push(clFla,conjuncts);
        conj_cnt++;
      }

      if (conj_cnt == 1) {
        interpolant = conjuncts->head();
        FormulaList::destroy(conjuncts);
      } else {
        interpolant = JunctionFormula::generalJunction(AND, conjuncts);
      }
    }

    // finish constructing the derivation
    {
      Inference elInf = NonspecificInferenceMany(InferenceRule::SAT_COLOR_ELIMINATION, second_prems);
      FormulaUnit* interpolated = new FormulaUnit(interpolant,elInf);

      UnitList::push(interpolated,first_prems);

      Inference finalInf = NonspecificInferenceMany(InferenceRule::SAT_COLOR_ELIMINATION,first_prems);
      Clause* foRef = Clause::fromIterator(LiteralIterator::getEmpty(), finalInf);

      throw MainLoop::RefutationFoundException(foRef);
    }
  }
}

SAT::Status SplittingBranchSelector::processDPConflicts()
{
  // ASS(_solver->getStatus()==SATSolver::SATISFIABLE);

  if(!_dp) {
    return Status::SATISFIABLE;
  }

  SAT2FO& s2f = _parent.satNaming();
  static LiteralStack gndAssignment;
  static LiteralStack unsatCore;

  while (true) { // breaks inside
    {
      TIME_TRACE("congruence closure");

      gndAssignment.reset();
      // collects only ground literals, because it known only about them ...
      s2f.collectAssignment(_solver, gndAssignment);
      // ... moreover, _dp->addLiterals will filter the set anyway

      _dp->reset();
      _dp->addLiterals(pvi( LiteralStack::ConstIterator(gndAssignment) ), false);
      DecisionProcedure::Status dpStatus = _dp->getStatus(true);

      if(dpStatus!=DecisionProcedure::UNSATISFIABLE) {
        break;
      }

      unsigned unsatCoreCnt = _dp->getUnsatCoreCount();
      for(unsigned i=0; i<unsatCoreCnt; i++) {
        unsatCore.reset();
        _dp->getUnsatCore(unsatCore, i);
        SATClause* conflCl = s2f.createConflictClause(unsatCore);
        _solver.addClause(conflCl);
      }

      RSTAT_CTR_INC("ssat_dp_conflict");
      RSTAT_CTR_INC_MANY("ssat_dp_conflict_clauses",unsatCoreCnt);
    }

    // there was conflict, so we try looking for a different model
    {
      TIME_TRACE(TimeTrace::AVATAR_SAT_SOLVER);
      if (_solver.solve() == Status::UNSATISFIABLE) {
        return Status::UNSATISFIABLE;
      }
    }
  }

  // ASS(_solver->getStatus()==SATSolver::SATISFIABLE);
  return Status::SATISFIABLE;
}

void SplittingBranchSelector::updateSelection(unsigned satVar, VarAssignment asgn,
    SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  ASS_NEQ(asgn, VarAssignment::NOT_KNOWN); //we always do full SAT solving, so there shouldn't be unknown variables

  SplitLevel posLvl = _parent.getNameFromLiteral(SATLiteral(satVar, true));
  SplitLevel negLvl = _parent.getNameFromLiteral(SATLiteral(satVar, false));

  bool posUsed = _parent.isUsedName(posLvl);
  bool negUsed = _parent.isUsedName(negLvl);

  switch(asgn) {
  case VarAssignment::TRUE:
    if(posUsed && !_selected.find(posLvl)) {
      _selected.insert(posLvl);
      addedComps.push(posLvl);
    }
    if(negUsed && _selected.find(negLvl)) {
      _selected.remove(negLvl);
      removedComps.push(negLvl);
    }
    break;
  case VarAssignment::FALSE:
    if(negUsed && !_selected.find(negLvl)) {
      _selected.insert(negLvl);
      addedComps.push(negLvl);
    }
    if(posUsed && _selected.find(posLvl)) {
      _selected.remove(posLvl);
      removedComps.push(posLvl);
    }
    break;
  case VarAssignment::DONT_CARE:
  {
    bool posSticky = posUsed && _parent.isSticky(posLvl);
    bool negSticky = negUsed && _parent.isSticky(negLvl);
    { // hardcoding (_eagerRemoval == true)
      if(posUsed && !posSticky && _selected.find(posLvl) ) {
        _selected.remove(posLvl);
        removedComps.push(posLvl);
      }
      if(negUsed && !negSticky && _selected.find(negLvl)) {
        _selected.remove(negLvl);
        removedComps.push(negLvl);
      }
    }
    if(posSticky && !_selected.find(posLvl) ) {
      _selected.insert(posLvl);
      addedComps.push(posLvl);
    }
    if(negSticky && !_selected.find(negLvl) ) {
      _selected.insert(negLvl);
      addedComps.push(negLvl);
    }
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

void SplittingBranchSelector::addSatClauseToSolver(SATClause* cl)
{
  cl = SATClause::removeDuplicateLiterals(cl);
  if(!cl) {
    RSTAT_CTR_INC("splitter_tautology");
    return;
  }

  RSTAT_CTR_INC("ssat_sat_clauses");
  _solver.addClause(cl);
}

void SplittingBranchSelector::recomputeModel(SplitLevelStack& addedComps, SplitLevelStack& removedComps)
{
  ASS(addedComps.isEmpty());
  ASS(removedComps.isEmpty());

  unsigned maxSatVar = _parent.maxSatVar();

  SAT::Status stat;
  {
    TIME_TRACE(TimeTrace::AVATAR_SAT_SOLVER);
    stat = _solver.solve();
  }
  if (stat == Status::SATISFIABLE) {
    stat = processDPConflicts();
  }
  if(stat == Status::UNSATISFIABLE) {
    handleSatRefutation(); // noreturn!
  }
  if(stat == Status::UNKNOWN){
    env.statistics->smtReturnedUnknown=true;
    throw MainLoop::MainLoopFinishedException(TerminationReason::REFUTATION_NOT_FOUND);
  }
  ASS_EQ(stat,Status::SATISFIABLE);

  for(unsigned i=1; i<=maxSatVar; i++) {
    VarAssignment asgn = _solver.getAssignment(i);

    /**
     * This may happen with the current version of z3 when evaluating expressions like (0 == 1/0).
     * A bug report / feature request has been sent to the z3 people, but this will make us stay sound in release mode.
     * (While violating an assertion in debug - see getAssignment in Z3Interfacing).
     */
    if (asgn == VarAssignment::NOT_KNOWN) {
      env.statistics->smtDidNotEvaluate=true;
      throw MainLoop::MainLoopFinishedException(TerminationReason::REFUTATION_NOT_FOUND);
    }

    updateSelection(i, asgn, addedComps, removedComps);
  }
}

//////////////
// Splitter
//////////////

std::string Splitter::splPrefix = "";

Splitter::Splitter()
: _deleteDeactivated(Options::SplittingDeleteDeactivated::ON), _branchSelector(*this),
  _clausesAdded(false)
{}

Splitter::~Splitter()
{
  while(_db.isNonEmpty()) {
    if(_db.top()) {
      delete _db.top();
    }
    _db.pop();
  }
}

const Options& Splitter::getOptions() const
{
  ASS(_sa);

  return _sa->getOptions();
}

Ordering& Splitter::getOrdering() const
{
  ASS(_sa);

  return _sa->getOrdering();
}


void Splitter::init(SaturationAlgorithm* sa)
{
  _sa = sa;

  const Options& opts = getOptions();
  _branchSelector.init();

  _showSplitting = opts.showSplitting();

  _complBehavior = opts.splittingAddComplementary();
  _nonsplComps = opts.splittingNonsplittableComponents();

  _congruenceClosure = opts.splittingCongruenceClosure();
  _shuffleComponents = opts.randomTraversals();

#if VZ3
  hasSMTSolver = (opts.satSolver() == Options::SatSolver::Z3);
#endif

  if (opts.splittingAvatimer() < 1.0) {
    unsigned timeLimit = opts.simulatedTimeLimit(); // is also stored in deciseconds
    if (timeLimit == 0) {
      timeLimit = opts.timeLimitInDeciseconds();
    }
    _stopSplittingAtTime = opts.splittingAvatimer() * timeLimit * 100;
#if VAMPIRE_PERF_EXISTS
    unsigned instrLimit = opts.simulatedInstructionLimit();
    if (instrLimit == 0) {
      instrLimit = opts.instructionLimit();
    }
    _stopSplittingAtInst = opts.splittingAvatimer() * instrLimit;
#endif
  } else {
    _stopSplittingAtTime = 0;
#if VAMPIRE_PERF_EXISTS
    _stopSplittingAtInst = 0;
#endif
  }

  _deleteDeactivated = opts.splittingDeleteDeactivated();
  _cleaveNonsplittables = opts.cleaveNonsplittables();

  // _componentIdx = new SubstitutionTreeClauseVariantIndex();
  _componentIdx = new HashingClauseVariantIndex();
}

SplitLevel Splitter::getNameFromLiteral(SATLiteral lit) const
{
  SplitLevel res = getNameFromLiteralUnsafe(lit);
  ASS_L(res, _db.size());
  return res;
}

/**
 * This function can be called with SAT literal for which the split
 * record is not created yet. In this case the result will be larger
 * than the size of _db.
 */
SplitLevel Splitter::getNameFromLiteralUnsafe(SATLiteral lit) const
{
  return (lit.var()-1)*2 + (lit.positive() ? 0 : 1);
}
SATLiteral Splitter::getLiteralFromName(SplitLevel compName)
{
  unsigned var = compName/2 + 1;
  bool polarity = (compName&1)==0;
  return SATLiteral(var, polarity);
}

std::string Splitter::getFormulaStringFromName(SplitLevel compName, bool negated)
{
  if (splPrefix.empty()) {
    if(env.options->proof()==Options::Proof::TPTP){
      unsigned spl = env.signature->addFreshFunction(0,"spl");
      splPrefix = env.signature->functionName(spl)+"_";
    }
  }

  SATLiteral lit = getLiteralFromName(compName);
  if (negated) {
    lit = lit.opposite();
  }
  return getFormulaStringFromLiteral(lit);
}

std::string Splitter::getFormulaStringFromLiteral(SATLiteral lit) {
  if (lit.positive()) {
    return splPrefix+Lib::Int::toString(lit.var());
  } else {
    return "~"+splPrefix+Lib::Int::toString(lit.var());
  }
}

Unit* Splitter::getDefinitionFromName(SplitLevel compName) const
{
  // always stored positively
  return _defs.get(compName & ~1);
}

void Splitter::collectDependenceLits(SplitSet* splits, SATLiteralStack& acc) const
{
  auto sit = splits->iter();
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    acc.push(getLiteralFromName(nm).opposite());
  }
}

Clause* Splitter::getComponentClause(SplitLevel name) const
{
  ASS_L(name,_db.size());
  ASS_NEQ(_db[name],0);

  return _db[name]->component;
}

Clause* Splitter::reintroduceAvatarAssertions(Clause* cl) {
  // This method can only be called when synthesizing programs
  ASS(env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
  RStack<Literal*> resLits;
  resLits->loadFromIterator(cl->iterLits());
  for (SplitLevel nm : iterTraits(cl->splits()->iter())) {
    Clause* compCl = getComponentClause(nm);
    // When synthesizing programs, all components are ground and hence unit
    ASS(compCl->length() == 1);
    resLits->push(Literal::complementaryLiteral((*compCl)[0]));
  }
  return Clause::fromStack(*resLits, Inference(SimplifyingInference1(InferenceRule::AVATAR_ASSERTION_REINTRODUCTION, cl)));
}

void Splitter::onAllProcessed()
{
  if(!_clausesAdded) {
    return;
  }
  _clausesAdded = false;

  static SplitLevelStack toAdd;
  static SplitLevelStack toRemove;

  toAdd.reset();
  toRemove.reset();

  _branchSelector.recomputeModel(toAdd, toRemove);

  if (_showSplitting) { // TODO: this is just one of many ways Splitter could report about changes
    std::cout << "[AVATAR] recomputeModel: + ";
    for (unsigned i = 0; i < toAdd.size(); i++) {
      std::cout << getLiteralFromName(toAdd[i]) << ",";
    }
    std::cout << "\t - ";
    for (unsigned i = 0; i < toRemove.size(); i++) {
      std::cout << getLiteralFromName(toRemove[i]) << ",";
    }
    std::cout << std::endl;
  }

  {
    TIME_TRACE("splitting model update"); // includes component removals and additions, also processing fast clauses and zero implied splits

    if(toRemove.isNonEmpty()) {
      removeComponents(toRemove);
    }
    if(toAdd.isNonEmpty()) {
      addComponents(toAdd);
    }
  }
}


bool Splitter::shouldAddClauseForNonSplittable(Clause* cl, unsigned& compName, Clause*& compCl)
{
  if((_congruenceClosure
#if VZ3
      || hasSMTSolver
#endif
      )
      && cl->length()==1 && (*cl)[0]->ground() ) {
    //we add ground unit clauses if we use congruence closure...
    // (immediately zero implied!)
    compName = tryGetComponentNameOrAddNew(cl->length(), cl->literals(), cl, compCl);
    RSTAT_CTR_INC("ssat_ground_clauses_for_congruence");
    return true;
  }

  if(_nonsplComps==Options::SplittingNonsplittableComponents::NONE) {
    return false;
  }

  if(!tryGetExistingComponentName(cl->length(), cl->literals(), compName, compCl)) {
    bool canCreate;
    switch(_nonsplComps) {
    case Options::SplittingNonsplittableComponents::ALL:
      canCreate = true;
      break;
    case Options::SplittingNonsplittableComponents::ALL_DEPENDENT:
      canCreate = !cl->splits()->isEmpty();
      break;
    case Options::SplittingNonsplittableComponents::KNOWN:
      canCreate = false;
      break;
    default:
      ASSERTION_VIOLATION;
    }
    if(!canCreate) {
      return false;
    }
    RSTAT_CTR_INC("ssat_non_splittable_introduced_components");
    compName = tryGetComponentNameOrAddNew(cl->length(), cl->literals(), cl, compCl);
  }
  ASS_NEQ(cl,compCl);

  // We only reach here if cl already exists as a component

  return true;
}

void Splitter::conjectureSingleton(Literal* theLit, Clause* orig)
{
  unsigned db_before = _db.size();

  Clause *compCl;
  SplitLevel compName = tryGetComponentNameOrAddNew(1, &theLit, orig, compCl);
  SATLiteral nameLit = getLiteralFromName(compName);
  _branchSelector.trySetTrue(nameLit);
  _db[compName]->sticky = true;

  // detect whether a component was added
  if(db_before < _db.size()) {
    if (_showSplitting)
      std::cout << "[AVATAR] conjectures: "<< compCl->toString() << std::endl;

    // we added a literal that we want to be true in the SAT solver
    // this isn't exactly adding a clause, but we want to recompute a model at some point soon
    _clausesAdded = true;
  }
}

bool Splitter::handleNonSplittable(Clause* cl)
{
  if (_cleaveNonsplittables && cl->length() > 1) {
    auto it = cl->iterLits();
    while (it.hasNext()) {
      conjectureSingleton(it.next(),cl);
    }
  }

  SplitLevel compName;
  Clause* compCl;
  if(!shouldAddClauseForNonSplittable(cl, compName, compCl)) {
    return false;
  }

  // OK, we will handle the clause, this means for the FO part we will pretend it was redundant
  // and instead we will record information about it in the SAT solver

  SplitRecord& nameRec = *_db[compName];
  ASS_EQ(nameRec.component,compCl);
  ASS_REP2(compCl->store()==Clause::NONE || compCl->store()==Clause::ACTIVE ||
      compCl->store()==Clause::PASSIVE || compCl->store()==Clause::UNPROCESSED, *compCl, compCl->store());

  if(nameRec.active && compCl->store()==Clause::NONE) {
    //we need to make sure the clause naming the component is present in this case, as the
    //following scenario may lead to incompleteness:
    //  component C is selected and put to unprocessed
    //  clause C' syntactically equal to C is derived and put into simplification container
    //  component C is made redundant by C'
    //  we name C' as C. The sat clause {C} won't lead to addition of C into FO as C is already selected.

    compCl->invalidateMyReductionRecords();
    _sa->addNewClause(compCl);
  }

  SplitSet* sset = cl->splits();
  ASS(sset->size()!=1 || _db[sset->sval()]->component!=cl);
  if(sset->member(compName)) {
    //we derived a component that depends on itself.
    //This derivation is therefore redundant, so we can skip it.
    // (would result in a propositional tautology)

    RSTAT_CTR_INC("ssat_self_dependent_component");
  } else {
    static SATLiteralStack satLits;
    satLits.reset();
    collectDependenceLits(cl->splits(), satLits);
    satLits.push(getLiteralFromName(compName));

    SATClause* nsClause = SATClause::fromStack(satLits);
    nsClause->sort();
    if(_already_added.contains(nsClause)) {
      delete nsClause;
      return true;
    }
    _already_added.insert(nsClause);

    UnitList* ps = 0;

    FormulaList* resLst=0;
    // do compName first
    UnitList::push(getDefinitionFromName(compName),ps);
    FormulaList::push(new NamedFormula(getFormulaStringFromName(compName)),resLst);

    // now do splits
    auto sit = cl->splits()->iter();
    while(sit.hasNext()) {
      SplitLevel nm = sit.next();
      UnitList::push(getDefinitionFromName(nm),ps);
      FormulaList::push(new NamedFormula(getFormulaStringFromName(nm,true /*negated*/)),resLst);
    }

    UnitList::push(cl,ps); // making sure this clause is the last one pushed (for the sake of colorFromAssumedFOConversion)

    Formula* f = JunctionFormula::generalJunction(OR,resLst);
    FormulaUnit* scl = new FormulaUnit(f,NonspecificInferenceMany(InferenceRule::AVATAR_SPLIT_CLAUSE,ps));
    if(env.options->proofExtra() == Options::ProofExtra::FULL)
      env.proofExtra.insert(scl, new SATClauseExtra(nsClause));

    nsClause->setInference(new FOConversionInference(scl));

    if (_showSplitting) {
      std::cout << "[AVATAR] registering a non-splittable: "<< cl->toString() << std::endl;
    }

    addSatClauseToSolver(nsClause);

    RSTAT_CTR_INC("ssat_non_splittable_sat_clauses");
  }

  return true;
}

/**
 * Since the component names in a clauses Splitset should be interpreted as propositional variables,
 * Splitter know how to do their proper printing.
 */
std::string Splitter::splitsToString(SplitSet* splits)
{
  std::ostringstream res;

  auto it = splits->iter();
  while(it.hasNext()) {
    res << getLiteralFromName(it.next());
    if(it.hasNext()) {
      res<<", ";
    }
  }
  return res.str();
}

/**
 * Takes Clause cl and attempts to split it into Components i.e. produces C1...Cn = cl such that
 * all Ci's have a pairwise disjoint set of variables and no Ci can be split further - the
 * splitting is maximal.
 *
 * Returns true if this is possible and false otherwise. The result is placed in acc.
 *
 * This is implemented using the Union-Find algorithm.
 *
 * Comment by Giles.
 */
bool Splitter::getComponents(Clause* cl, Stack<LiteralStack>& acc, bool shuffle)
{
  ASS_EQ(acc.size(), 0);

  unsigned clen=cl->length();
  ASS_G(clen,0);

  if(clen<=1) {
    return false;
  }

  //Master literal of an variable is the literal
  //with lowest index, in which it appears.
  static DHMap<unsigned, unsigned, IdentityHash, DefaultHash> varMasters;
  varMasters.reset();
  IntUnionFind components(clen);

  for(unsigned i=0;i<clen;i++) {
    Literal* lit=(*cl)[i];
    VariableIterator vit(lit);
    while(vit.hasNext()) {
      unsigned master=varMasters.findOrInsert(vit.next().var(), i);
      if(master!=i) {
        components.doUnion(master, i);
      }
    }
  }
  components.evalComponents();

  unsigned compCnt=components.getComponentCount();

  if(compCnt==1) {
    return false;
  }

  env.statistics->splitClauses++;
  env.statistics->splitComponents+=compCnt;

  IntUnionFind::ComponentIterator cit(components);
  ASS(cit.hasNext());
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator elit=cit.next();

    acc.push(LiteralStack());

    while(elit.hasNext()) {
      int litIndex=elit.next();
      Literal* lit = (*cl)[litIndex];

      acc.top().push(lit);
    }
  }
  ASS_EQ(acc.size(),compCnt);
  if (shuffle) {
    Shuffling::shuffleArray(acc.begin(),compCnt);
  }
  return true;
}


/**
 * Attempt to split clause @b cl, and return true if successful
 */
bool Splitter::doSplitting(Clause* cl)
{
  static bool hasStopped = false;
  if (hasStopped) {
    return false;
  }
  // When synthesizing programs:
  // if this clause contains an answer literal or is not computable, don't split it
  static bool synthesis = (env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS);
  if (synthesis && (cl->hasAnswerLiteral() || !static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->isComputable(cl))) {
    return false;
  }
  if ((_stopSplittingAtTime && (unsigned)Timer::elapsedMilliseconds() >= _stopSplittingAtTime)
#if VAMPIRE_PERF_EXISTS
    || (_stopSplittingAtInst && Timer::elapsedMegaInstructions() >= _stopSplittingAtInst)
#endif
    ) {
    if (_showSplitting) {
      std::cout << "[AVATAR] Stopping the splitting process."<< std::endl;
    }
    hasStopped = true;
    return false;
  }

  //!! this check is important or we might end up looping !!
  if(cl->isComponent()) {
    return false;
  }

  static Stack<LiteralStack> comps;
  comps.reset();
  // fills comps with components, returning if not splittable
  if(!getComponents(cl, comps, _shuffleComponents)) {
    return handleNonSplittable(cl);
  }

  static SATLiteralStack satClauseLits;
  satClauseLits.reset();

  // Add literals for existing constraints
  collectDependenceLits(cl->splits(), satClauseLits);

  UnitList* ps = 0;
  FormulaList* resLst=0;

  unsigned compCnt = comps.size();
  for(unsigned i=0; i<compCnt; ++i) {
    const LiteralStack& comp = comps[i];

    if (_cleaveNonsplittables && comp.size() > 1) {
      auto it = comp.iter();
      while (it.hasNext()) {
        conjectureSingleton(it.next(),cl);
      }
    }

    Clause* compCl;
    SplitLevel compName = tryGetComponentNameOrAddNew(comp, cl, compCl);
    SATLiteral nameLit = getLiteralFromName(compName);
    satClauseLits.push(nameLit);

    UnitList::push(getDefinitionFromName(compName),ps);
    FormulaList::push(new NamedFormula(getFormulaStringFromName(compName)),resLst);
  }

  SATClause* splitClause = SATClause::fromStack(satClauseLits);

  if (_showSplitting) {
    std::cout << "[AVATAR] split a clause: "<< cl->toString() << std::endl;
  }

  // now do splits
  auto sit = cl->splits()->iter();
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    UnitList::push(getDefinitionFromName(nm),ps);
    FormulaList::push(new NamedFormula(getFormulaStringFromName(nm,true /*negated*/)),resLst);
  }

  UnitList::push(cl,ps); // making sure this clause is the last one pushed (for the sake of colorFromAssumedFOConversion)

  Formula* f = JunctionFormula::generalJunction(OR,resLst);
  FormulaUnit* scl = new FormulaUnit(f,NonspecificInferenceMany(InferenceRule::AVATAR_SPLIT_CLAUSE,ps));
  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(scl, new SATClauseExtra(splitClause));

  splitClause->setInference(new FOConversionInference(scl));

  addSatClauseToSolver(splitClause);

  return true;
}

/**
 * Uses _componentIdx to search for an existing name for the component represented by @b lits
 *
 * @param size number of literals in component
 * @param lits literals of component
 * @param comp the existing propositional name (SplitLevel) for this component - to be filled
 * @param compCl the existing clause for this component - to be filled
 * @return True if the component already exists
 *
 * @author Giles
 */
bool Splitter::tryGetExistingComponentName(unsigned size, Literal* const * lits, SplitLevel& comp, Clause*& compCl)
{
  ClauseIterator existingComponents;
  {
    TIME_TRACE("splitting component index usage");
    existingComponents = _componentIdx->retrieveVariants(lits, size);
  }

  if(!existingComponents.hasNext()) {
    return false;
  }
  compCl = existingComponents.next();
  ASS(!existingComponents.hasNext());
  comp = compCl->splits()->sval();
  return true;
}

/**
 * Records a new component. This involves
 * - Building a new Clause for the component as a AVATAR_COMPONENT
 * - Create a SplitRecord for the component
 * - Record the name in the splits of the clause
 * - Insert the clause into _componentIdx for variant checking later
 *
 * @param name The propositional name for the component to add
 * @param size The number of literals in the component to add
 * @param lits The literals in the component to add
 * @param orig The original clause i.e. the one that we are splitting
 *
 * Comment by Giles.
 */
Clause* Splitter::buildAndInsertComponentClause(SplitLevel name, unsigned size, Literal* const * lits, Clause* orig)
{
  ASS_EQ(_db[name],0);
  ASS(orig)

  /**
   * retrieve or prepare a definition formula as in "4 <=> sP0(n0)"
   * the name is always taken positively (like 4) even when we are introducing a negated ground component (like ~sP0(n0))
   * so we potentially need to a complementary literal (it's always a ground singleton in such case) for the rhs formula
   */
  SplitLevel posName = (name&~1);
  Unit* def_u;
  UnitInputType inpType = orig->inputType();
  if (!_defs.find(posName, def_u)) {
    Literal* oplit;
    Literal*const* possibly_flipped_lits = lits;
    if (size == 1 && lits[0]->ground() && lits[0]->isNegative()) {
      oplit = Literal::complementaryLiteral(lits[0]);
      possibly_flipped_lits = &oplit;
    }

    std::string formula_name = getFormulaStringFromName(posName);
    Clause* temp = Clause::fromIterator(arrayIter(possibly_flipped_lits, size),
        NonspecificInference0(inpType,InferenceRule::AVATAR_DEFINITION));
    Formula* def_f = new BinaryFormula(IFF,
                 new NamedFormula(formula_name),
                 Formula::fromClause(temp));

    Inference def_u_i = NonspecificInference0(inpType,InferenceRule::AVATAR_DEFINITION);
    // def_u_i.setPureTheoryDescendant(orig->isPureTheoryDescendant()); -- don't probapagate PureTheoryDescendant through avatar
    // e.g. when a PureTheoryDescendant ~$less(X1,$sum(X1,1)) | ~$less(X0,X0) splits, the component ~$less(X1,$sum(X1,1)) is not longer a theory lemma
    def_u_i.setInductionDepth(orig->inference().inductionDepth());
    def_u = new FormulaUnit(def_f,def_u_i);
    InferenceStore::instance()->recordIntroducedSplitName(def_u,formula_name);
    // cout << "Add def " << def_u->toString() << " for " << name << endl;
    ALWAYS(_defs.insert(posName,def_u));
  }

  Clause* compCl = Clause::fromIterator(arrayIter(lits, size),
          NonspecificInference1(InferenceRule::AVATAR_COMPONENT,def_u));

  if(posName == name && env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(def_u, new SplitDefinitionExtra(compCl));

  // propagate running sums:
  // - we have certain values we propagate from the parents of a clause d to d. These values are mainly used to guide saturation.
  // - a component-clause has no parents, but it is still very related to the original clause (that is, the clause which we split).
  // - for a component-clause d it is a priori not clear whether we should
  //   1) give d certain initial values (since d has no parents), or
  //   2) treat the original clause as parent, and therefore propagate the values from the original clause to d.
  compCl->setAge(orig->age());
  compCl->inference().th_ancestors = orig->inference().th_ancestors;
  compCl->inference().all_ancestors = orig->inference().all_ancestors;
  compCl->inference().setSineLevel(orig->inference().getSineLevel());

  _db[name] = new SplitRecord(compCl);
  compCl->setSplits(SplitSet::getSingleton(name));
  compCl->setComponent(true);

  if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
    // in this mode, compCl is assumed to be a child since the beginning of times
    _db[name]->children.push(compCl);
    // (with _deleteDeactivated on, compCl is always inserted anew on activation)
  }

  {
    TIME_TRACE("splitting component index maintenance");
    _componentIdx->insert(compCl);
  }

  return compCl;
}

SplitLevel Splitter::addNonGroundComponent(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  ASS_REP(_db.size()%2==0, _db.size());
  ASS_G(size,0);
  ASS(forAll(arrayIter(lits, size), 
          [] (Literal* l) { return !l->ground(); } )); //none of the literals can be ground

  SATLiteral posLit(_sat2fo.createSpareSatVar(), true);
  SplitLevel compName = getNameFromLiteralUnsafe(posLit);
  ASS_EQ(compName&1,0); //positive levels are even
  ASS_GE(compName,_db.size());
  _db.push(0);
  _db.push(0);
  ASS_L(compName,_db.size());

  _branchSelector.updateVarCnt();
  _branchSelector.considerPolarityAdvice(posLit);

  compCl = buildAndInsertComponentClause(compName, size, lits, orig);

  return compName;
}

SplitLevel Splitter::addGroundComponent(Literal* lit, Clause* orig, Clause*& compCl)
{
  ASS_REP(_db.size()%2==0, _db.size());
  ASS(lit->ground());

  SATLiteral satLit = _sat2fo.toSAT(lit);
  SplitLevel compName = getNameFromLiteralUnsafe(satLit);

  if(compName>=_db.size()) {
    _db.push(0);
    _db.push(0);
  }
  else {
    ASS_EQ(_complBehavior,Options::SplittingAddComplementary::NONE); 
    //otherwise the complement would have been created below ...
    // ... in the respective previous pass through this method 
  }
  ASS_L(compName,_db.size());

  if(_complBehavior!=Options::SplittingAddComplementary::NONE) {
    //we insert both literal and its negation
    unsigned oppName = compName^1;
    ASS_L(oppName,_db.size());
    Literal* opposite = Literal::complementaryLiteral(lit);
    buildAndInsertComponentClause(oppName, 1, &opposite, orig);
  }
  compCl = buildAndInsertComponentClause(compName, 1, &lit, orig);

  _branchSelector.updateVarCnt();
  _branchSelector.considerPolarityAdvice(satLit);

  return compName;
}

/**
 * @param orig original clause (one being split) used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 * @param comp Component (Record) that we're getting the name for
 * @param compCl The clause that will be used to represent this component - to be filled
 *
 * @return the propositional name for the Clause (to be passed to the SAT solver)
 */
SplitLevel Splitter::tryGetComponentNameOrAddNew(const LiteralStack& comp, Clause* orig, Clause*& compCl)
{
  return tryGetComponentNameOrAddNew(comp.size(), comp.begin(), orig, compCl);
}

/**
 * @param orig original clause (one being split) used to determine input type of the component.
 *             Can be zero, in that case the input type is Unit::AXIOM
 * @param size The number of literals in the component
 * @param lits The component to be named (as an array of literals)
 * @param compCl The clause that will be used to represent this component - to be filled
 *
 * @return the propositional name for the Clause (to be passed to the SAT solver)
 */
SplitLevel Splitter::tryGetComponentNameOrAddNew(unsigned size, Literal* const * lits, Clause* orig, Clause*& compCl)
{
  SplitLevel res;

  if(tryGetExistingComponentName(size, lits, res, compCl)) {
    RSTAT_CTR_INC("ssat_reused_components");
  }
  else {
    RSTAT_CTR_INC("ssat_new_components");

    // adding a component should mean "recompute model" (even if we actually don't end up adding a clause)
    // this is connected to the subtle case in handleNonSplittable
    // and the fact we now maintain the _already_added filter and don't add a clause for second time there
    // (the case where this might be needed is for a (conditional) ground clause
    // swallowed up by handleNonSplittable, while the corresponding prop variable is already true in the model,
    // because the complementary component was already introduced and considered in the past - requires aac=none to manifest)
    _clausesAdded = true;

    if(size==1 && lits[0]->ground()) {
      res = addGroundComponent(lits[0], orig, compCl);
    }
    else {
      res = addNonGroundComponent(size, lits, orig, compCl);
    }
  }
  return res;
}

static const int NOT_WORTH_REINTRODUCING = 0;

/**
 * Assign the @b SplitSet @b splits to the clause @b cl.
 */
void Splitter::assignClauseSplitSet(Clause* cl, SplitSet* splits)
{
  ASS(!cl->splits());
    
  cl->setSplits(splits);

  //update "children" field of relevant SplitRecords
  auto bsit = splits->iter();
  bool should_reintroduce = false;
  unsigned cl_weight = cl->weight();
  while(bsit.hasNext()) {
    SplitLevel slev=bsit.next();
    _db[slev]->children.push(cl);    
    if (cl_weight <= _db[slev]->component->weight()) {
      should_reintroduce = true;
    }
  }  
  
  /**
   * Heuristic idea -- only if the clause is lighter than at least
   * one of the component clauses on which it depends, 
   * it will be kept for reintroduction.
   */
  if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
    cl->setNumActiveSplits(
      (_deleteDeactivated == Options::SplittingDeleteDeactivated::OFF || should_reintroduce) ? 
        splits->size() : NOT_WORTH_REINTRODUCING);
  }
}

/**
 * Register the reduction of the @b cl clause
 *
 * At this stage we also check for zero-implied literals and remove
 * them if found, this is safe as we no longer rely on them
 */
void Splitter::onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement)
{
  ASS(cl);

  if(!premises.hasNext()) {
    ASS(!replacement || cl->splits()==replacement->splits() ||
        ((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) && cl->hasAnswerLiteral() && (replacement->inference().rule() == InferenceRule::AVATAR_ASSERTION_REINTRODUCTION || replacement->inference().rule() == InferenceRule::ANSWER_LITERAL_REMOVAL)));
    return;
  }

  SplitSet* unionAll;
  if(replacement) {
    unionAll = replacement->splits();
    ASS(forAll(premises, 
            [replacement] (Clause* premise) { 
              //SplitSet* difference = premise->splits()->subtract(replacement->splits());
              //if(difference->isEmpty()) return true; // isSubsetOf true
              // Now check if those in the difference are zero implied
              //auto dsit = difference->iter();
              //while(dsit.hasNext()){
              //  SplitLevel sl = dsit.next();
                // check if zero-implied
              //  SATLiteral sat_lit = getLiteralFromName(sl);
              //  if(!_branchSelector.isZeroImplied(sat_lit)) return false;
              //}
              //return true; // all okay
              return premise->splits()->isSubsetOf(replacement->splits()); 
            } ));
  } else {
    Clause* premise0 = premises.next();
    unionAll=premise0->splits();
    while(premises.hasNext()) {
      Clause* premise=premises.next();
      ASS(premise);
      unionAll=unionAll->getUnion(premise->splits());
    }
  }
  SplitSet* diff=unionAll->subtract(cl->splits());      
        
  ASS(allSplitLevelsActive(diff));

  if(diff->isEmpty()) {
    // unconditionally reduced
    if (_deleteDeactivated != Options::SplittingDeleteDeactivated::ON) {
      if (!cl->isComponent()) {
        // a component always needs to stay in children (whenever _deleteDeactivated != Options::SplittingDeleteDeactivated::ON),
        // since it might be needed later as a proxy for the very clause which is (unconditionally) reducing it here!
        // (see also the special case in handleNonsplittable)

        // let others know not to keep the clause in children
        cl->setNumActiveSplits(NOT_WORTH_REINTRODUCING);
      }
    }

    return;
  }
  // else freeze clause

  // TODO: keep statistics in release ?
//#if VDEBUG
  RSTAT_CTR_INC("total_frozen");
//#endif

  cl->invalidateMyReductionRecords();
  auto dit = diff->iter();
  while(dit.hasNext()) {
    SplitLevel slev=dit.next();
    _db[slev]->addReduced(cl);
  }
}

void Splitter::addPartialRedundancyEntry(SplitSet* splits, PartialRedundancyEntry* e)
{
  auto sit = splits->iter();
  while (sit.hasNext()) {
    SplitLevel slev=sit.next();
    e->obtain();
    _db[slev]->partialRedundancyEntries.push(e);
  }
}

bool Splitter::allSplitLevelsActive(SplitSet* s)
{
  auto sit = s->iter();
  while(sit.hasNext()) {
    SplitLevel lev=sit.next();
    ASS_REP(lev<_db.size(), lev);
    ASS_REP(_db[lev]!=0, lev);
    if (!_db[lev]->active) {
      return false;
    }
  }
  return true;
}

void Splitter::onNewClause(Clause* cl)
{
  // when using AVATAR, we could have performed
  // generating inferences on the clause previously,
  // so we need to reset the data.
  PartialRedundancyHandler::destroyClauseData(cl);

  if (cl->inference().rule() == InferenceRule::AVATAR_ASSERTION_REINTRODUCTION) {
    // Do not assign splits from premises if cl originated by re-introducing AVATAR assertions (avoids looping)
    assignClauseSplitSet(cl, SplitSet::getEmpty());
  } else {
    if(!cl->splits()) {
      SplitSet* splits=getNewClauseSplitSet(cl);
      assignClauseSplitSet(cl, splits);
    }

    if (env.colorUsed) {
      SplitSet* splits = cl->splits();

      Color color = cl->color();

      auto it = splits->iter();
      while(it.hasNext()) {
        SplitLevel lv=it.next();
        SplitRecord* sr=_db[lv];

        color = static_cast<Color>(color | sr->component->color());
      }

      cl->updateColor(color);
    }
  }

  ASS(allSplitLevelsActive(cl->splits()));  
}

/**
 * Return a split set of a new clause
 *
 * Assumes that clauses referred to by cl->inference() object
 * are actual premises of @b cl. (This holds when BDDs are not
 * used.)
 */
SplitSet* Splitter::getNewClauseSplitSet(Clause* cl)
{
  SplitSet* res;
  Inference& inf= cl->inference();
  Inference::Iterator it=inf.iterator();

  res=SplitSet::getEmpty();

  while(inf.hasNext(it)) {
    Unit* premu=inf.next(it);
    if(!premu->isClause()) {
      //the premise comes from preprocessing
      continue;
    }
    Clause* prem=static_cast<Clause*>(premu);
    if(!prem->splits()) {
      //the premise comes from preprocessing
      continue;
    }
    res=res->getUnion(prem->splits());
  }
  return res;
}


Splitter::SplitRecord::~SplitRecord()
{
  component->decRefCnt();
  while(reduced.isNonEmpty()) {
    Clause* cl = reduced.pop().clause;
    cl->decRefCnt();
  }
}

/**
 * Add a reduced clause to the @b SplitRecord object.
 */
void Splitter::SplitRecord::addReduced(Clause* cl)
{
  cl->incRefCnt(); //dec when popped from the '_db[slev]->reduced' stack in backtrack method
  reduced.push(ReductionRecord(cl));
}

void Splitter::addSatClauseToSolver(SATClause* cl) {
  _clausesAdded = true;
  _branchSelector.addSatClauseToSolver(cl);
}

bool Splitter::handleEmptyClause(Clause* cl)
{
  if(cl->splits()->isEmpty()) {
    return false;
  }

  static SATLiteralStack conflictLits;
  conflictLits.reset();

  collectDependenceLits(cl->splits(), conflictLits);
  SATClause* confl = SATClause::fromStack(conflictLits);

  FormulaList* resLst=0;

  auto sit = cl->splits()->iter();
  while(sit.hasNext()) {
    SplitLevel nm = sit.next();
    FormulaList::push(new NamedFormula(getFormulaStringFromName(nm,true /*negated*/)),resLst);
  }

  Formula* f = JunctionFormula::generalJunction(OR,resLst);
  FormulaUnit* scl = new FormulaUnit(f,NonspecificInference1(InferenceRule::AVATAR_CONTRADICTION_CLAUSE,cl));
  if(env.options->proofExtra() == Options::ProofExtra::FULL)
    env.proofExtra.insert(scl, new SATClauseExtra(confl));

  confl->setInference(new FOConversionInference(scl));

  addSatClauseToSolver(confl);

  if (_showSplitting) {
    std::cout << "[AVATAR] proved ";
    auto sit = cl->splits()->iter();
    while(sit.hasNext()){
      std::cout << (_db[sit.next()]->component)->toString();
      if(sit.hasNext()){ std::cout << " | "; }
    }
    std::cout << endl;
  }

  env.statistics->satSplitRefutations++;
  return true;
}


void Splitter::addComponents(const SplitLevelStack& toAdd)
{
  SplitLevelStack::ConstIterator slit(toAdd);
  while(slit.hasNext()) {
    SplitLevel sl = slit.next();
    SplitRecord* sr = _db[sl];
    ASS(sr);
    ASS(!sr->active);
    sr->active = true;

    if (_deleteDeactivated == Options::SplittingDeleteDeactivated::ON) {
      ASS(sr->children.isEmpty());
      //we need to put the component clause among children,
      //so that it is backtracked when we remove the component
      sr->children.push(sr->component);
      _sa->addNewClause(sr->component);
    } else {
      // children were kept, so we just put them back
      RCClauseStack::Iterator chit(sr->children);
      while (chit.hasNext()) {
        Clause* cl = chit.next();
        cl->incNumActiveSplits();
        if (cl->getNumActiveSplits() == (int)cl->splits()->size()) {
          _sa->addNewClause(cl);
          //check that restored clause does not depend on inactive splits
          ASS(allSplitLevelsActive(cl->splits()));
        }
      }
    }
  }
}

/**
 * Perform backtracking of split levels in @c toRemove.
 *
 * Can be called only when there are no unprocessed clauses left.
 * This is to allow for easy clause removal from the saturation algorithm.
 */
void Splitter::removeComponents(const SplitLevelStack& toRemove)
{
  ASS(_sa->clausesFlushed());

  SplitSet* backtracked = SplitSet::getFromArray(toRemove.begin(), toRemove.size());

  // ensure all children are backtracked
  // i.e. removed from _sa and reference counter dec
  auto blit = backtracked->iter();
  while(blit.hasNext()) {
    SplitLevel bl=blit.next();
    SplitRecord* sr=_db[bl];
    ASS(sr);

    RCClauseStack::DelIterator chit(sr->children);
    while (chit.hasNext()) {
      Clause* ccl=chit.next();
      ASS(ccl->splits()->member(bl));
      if(ccl->store()!=Clause::NONE) {
        _sa->removeActiveOrPassiveClause(ccl);
        ASS_EQ(ccl->store(), Clause::NONE);
      } else {
      }
      ccl->invalidateMyReductionRecords();
      ccl->decNumActiveSplits();
      if (ccl->getNumActiveSplits() < NOT_WORTH_REINTRODUCING) {
        RSTAT_CTR_INC("unworthy child removed");
        chit.del();
      }
    }

    if (_deleteDeactivated == Options::SplittingDeleteDeactivated::ON) {
      sr->children.reset();
    }

    while (sr->partialRedundancyEntries.isNonEmpty()) {
      auto pre = sr->partialRedundancyEntries.pop();
      pre->deactivate();
      pre->release();
    }
  }

  // perform unfreezing

  // pick all reduced clauses (if the record relates to most recent reduction)
  // and them add back to _sa using addNewClause - this will get put to unprocessed
  auto blit2 = backtracked->iter();
  while(blit2.hasNext()) {
    SplitLevel bl=blit2.next();
    SplitRecord* sr=_db[bl];

    while(sr->reduced.isNonEmpty()) {
      ReductionRecord rrec=sr->reduced.pop();
      Clause* rcl=rrec.clause;
      if(rcl->validReductionRecord(rrec.timestamp)) {
        ASS(!rcl->splits()->hasIntersection(backtracked));
        ASS_EQ(rcl->store(), Clause::NONE);

        rcl->invalidateMyReductionRecords(); // to make sure we don't unfreeze this clause a second time
        _sa->addNewClause(rcl);

        // TODO: keep statistics in release ?
        // RSTAT_MCTR_INC("unfrozen clauses",rcl->getFreezeCount());
        RSTAT_CTR_INC("total_unfrozen");
#if VDEBUG
        //check that restored clause does not depend on inactive splits
        ASS(allSplitLevelsActive(rcl->splits()));
#endif
      }
      rcl->decRefCnt(); //inc when pushed on the 'sr->reduced' stack in Splitter::SplitRecord::addReduced
    }

    ASS(sr->active);
    sr->active = false;
  }
}

/**
 * Given a set of clauses (as obtained by saturation)
 * add in front of that list the component clauses currently assumed true in our (last) model.
 *
 * Also, make the list duplicate free (as far as pointer equality goes).
 * This means some links in <clauses> might get freed.
 */
UnitList* Splitter::preprendCurrentlyAssumedComponentClauses(UnitList* clauses)
{
  DHSet<Clause*> seen;

  // to keep the nice order
  UnitList::FIFO res;

  ArraySet::Iterator ait(_branchSelector._selected);
  while(ait.hasNext()) {
    unsigned level = ait.next();
    Clause* cl = getComponentClause(level);

    //cout << "selected level: " level << " has clause: " << cl->toString() << endl;
    seen.insert(cl);
    res.pushBack(cl);
  }

  // OK, for simplicity's sake, let's not even try keeping any of the old links
  UnitList::DestructiveIterator uit(clauses);
  while (uit.hasNext()) {
    Unit* u  = uit.next();
    Clause* cl = u->asClause();

    if (seen.insert(cl)) {
      // cout << "a new guy: " << cl->toString() << endl;
      res.pushBack(cl);
    } else {
      // cout << "seen already: " << cl->toString() << endl;
    }
  }

  return res.list();
}

}
