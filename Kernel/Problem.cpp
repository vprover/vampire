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
 * @file Kernel/Problem.cpp
 * Implements class Problem.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"

#include "Clause.hpp"
#include "Term.hpp"

#include "Problem.hpp"

#undef LOGGING
#define LOGGING 0

// added for the sake of ProofTracer
#include "Lib/VString.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Parse/TPTP.hpp"

#include <unordered_map>
#include <fstream>

using namespace Kernel;



// inferences that work on clauses;
static const DHMap<vstring, ProofTracer::InferenceKind> inference_info = {
    {"subsumption_resolution", ProofTracer::SIMPLIFYING},
    {"cnf_transformation", ProofTracer::ICP},
    {"trivial_inequality_removal", ProofTracer::TRIVSIMP},
    {"superposition", ProofTracer::GENERATING},
    {"forward_demodulation", ProofTracer::SIMPLIFYING},
    {"backward_demodulation", ProofTracer::SIMPLIFYING},
    {"resolution", ProofTracer::GENERATING},
    {"definition_unfolding", ProofTracer::ICP},

};

void ProofTracer::onInputClause(Clause* cl)
{
  CALL("ProofTracer::onInputClause");

  cout << "Init " << cl->toString() << endl;

  Clause* match = _tp->findVariant(cl);
  if (match != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(match);
    cout << " matched " << info->_name << endl;
    info->makeNew();
    _tp->initalBorn();
  }
}

void ProofTracer::onInputFinished()
{
  CALL("ProofTracer::onInputFinished");

  cout << "Input finished" << endl;

  _tp->onInputFinished();
}

ProofTracer::ParsedProof* ProofTracer::getParsedProof(const vstring& proofFileName)
{
  CALL("ProofTracer::getProof");

  ParsedProof* resultProof = new ParsedProof();

  istream* input;
  {
    // CAREFUL: this might not be enough if the ifstream (re)allocates while being operated
    BYPASSING_ALLOCATOR;

    input=new ifstream(proofFileName.c_str());
    if (input->fail()) {
      USER_ERROR("Cannot open problem file: "+proofFileName);
    }
  }

  Parse::TPTP parser(*input);

  parser.setUnitSourceMap(&resultProof->sources);

  // make the parser store axiomsNames for us here (for now)
  ScopedLet<DHMap<unsigned, vstring>*> axiomNamesSwap(Parse::TPTP::_axiomNames,&resultProof->names);

  try{
    parser.parse();
  }
  catch (UserErrorException& exception) {
    vstring msg = exception.msg();
    throw Parse::TPTP::ParseErrorException(msg,parser.lineNumber());
  }

  resultProof->units = parser.units();

  return resultProof;
}

Clause* ProofTracer::unitToClause(Unit* u)
{
  CALL("ProofTracer::unitToClause");

  Formula* f = static_cast<FormulaUnit*>(u)->formula();

  // cout << f->toString() << endl;

  if (f->connective() == FALSE) {
    return new(0) Clause(0,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
  }

  if (f->connective() == FORALL) {
    // ignore one forall and jump directly to the disjunction
    f = f->qarg();
  }

  Clause* res;

  // the singleton case
  if (f->connective() == LITERAL) {
    res = new(1) Clause(1,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
    (*res)[0] = f->literal();
    return res;
  }

  ASS_EQ(f->connective(),OR);
  FormulaList* args = f->args();
  unsigned len = FormulaList::length(args);
  res = new(len) Clause(len,NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT));
  unsigned idx = 0;
  for (;args != nullptr; args = args->tail()) {
    Formula* arg = args->head();
    ASS_EQ(arg->connective(),LITERAL);
    (*res)[idx++] = arg->literal();
  }

  return res;
}

ProofTracer::TracedProof* ProofTracer::prepareTracedProof(ProofTracer::ParsedProof* pp)
{
  CALL("ProofTracer::prepareTracedProof");

  DHMap<vstring,Clause*> clausesByNames;
  // a temp structure to be filled up during the first pass of the following loop and used after (when clauses have names)
  DHMap<vstring,Stack<vstring>> rememberedPremises;

  TracedProof *tp = new TracedProof;

  // we assume the units in pp->units come in topological order

  // names that should be processed
  DHSet<vstring> todo;

  ASS(pp->units); // have at least the empty clause in the proof
  FormulaUnit* theEmpty = static_cast<FormulaUnit*>(pp->units->head());
  ASS(theEmpty->formula()->connective() == FALSE); // the empty clause
  todo.insert(pp->names.get(theEmpty->number()));

  for (UnitList* units = pp->units; units != 0;units = units->tail()) {
    Unit* u = units->head();
    vstring uname;

    // cout << "Proof unit: " << u->toString() << endl;

    if (pp->names.find(u->number())) {
      uname = pp->names.get(u->number());
    } else { // the TPTP parser was very agile and negated a conjecture formula (and the proof printer had also been very agile and printed it with the conjecture role into the proof)
      Inference& i = u->inference();
      ASS_EQ(i.rule(),InferenceRule::NEGATED_CONJECTURE);
      Inference::Iterator it = i.iterator();
      ASS(i.hasNext(it));
      u = i.next(it);
      ASS(!i.hasNext(it));
      units->setHead(u);

      // we took the original (unnegated) formula instead
      // cout << "Corrected to: " << u->toString() << endl;
      uname = pp->names.get(u->number());
    }
    // cout << "Named: " << uname << endl;

    if (!todo.contains(uname)) {
      continue;
    }

    InferenceKind ik = ICP;
    Stack<vstring> premises; // empty by default

    Parse::TPTP::SourceRecord* rec = pp->sources.get(u);
    if (rec->isFile()) {
      // Parse::TPTP::FileSourceRecord* frec = static_cast<Parse::TPTP::FileSourceRecord*>(rec);
      // cout << "Has FSR: " << frec->fileName << " " << frec->nameInFile << endl;

      // no premises from here
      // is this case even possible? I guess yes for a cnf input?
    } else {
      Parse::TPTP::InferenceSourceRecord* irec = static_cast<Parse::TPTP::InferenceSourceRecord*>(rec);
      // cout << "Has ISR: " << irec->name << endl;

      ik = inference_info.get(irec->name);

      if (ik > ICP) { // we want to load also the guys u came about from
        for (unsigned i = 0; i < irec->premises.size(); i++) {
          // cout << " p: " << irec->premises[i] << endl;
          todo.insert(irec->premises[i]);
        }
        premises = std::move(irec->premises);
      } else {
        // this is either clausification or the original problem was already in cnf
        // so we ignore the premises here and make such units source nodes
      }
    }

    Clause* cl = unitToClause(u);

    // cout << "CL:" << cl->toString() << endl;

    ALWAYS(clausesByNames.insert(uname,cl));
    if (premises.size() > 0) {
      ALWAYS(rememberedPremises.insert(uname,std::move(premises)));
    }

    tp->regNewClause(cl,uname,ik);
    // cout << uname << " " << ik << " " << cl->toString() << endl;

    if (cl->isEmpty()) {
      tp->setEmpty(cl);
    }

    // cout << endl;
  }
  // cout << endl;

  // TODO: MANY things inside pp are still leaking
  delete pp;

  DHMap<vstring,Stack<vstring>>::Iterator it(rememberedPremises);
  while(it.hasNext()) {
    vstring uname;
    Stack<vstring>& premises = it.nextRef(uname);

    // cout << "uname " << uname << endl;
    Clause* child = clausesByNames.get(uname);

    for (unsigned i=0; i < premises.size(); i++) {
      vstring& prem = premises[i];

      // cout << "prem " << prem << endl;

      Clause* parent = clausesByNames.get(prem);

      tp->regChildParentPair(child,parent);
      /*
      cout << "pair" << endl;
      cout << child->toString() << endl;
      cout << parent->toString() << endl;
      cout << endl;
      */
    }
  }

  return tp;
}

void ProofTracer::TracedProof::init()
{
  CALL("ProofTracer::TracedProof::init");

  DHMap<Clause*, TracedClauseInfo*>::Iterator it(_clInfo);
  while (it.hasNext()) {
    Clause* cl;
    TracedClauseInfo* info;
    it.next(cl,info);

    ASS_EQ((cl == _theEmpty),info->isTerminal()); // exactly the Empty is Terminal

    if (info->isInital()) {
      _unbornInitials++;
    }
  }

  cout << "TracedProof initilized!" << endl;
  cout << "proof size: " << _clInfo.size() << endl;
  cout << "_unbornInitials: " << _unbornInitials << endl;
}

void ProofTracer::TracedProof::onInputFinished()
{
  CALL("ProofTracer::TracedProof::onInputFinished");

  cout << "_unbornInitials: " << _unbornInitials << endl;
  if (_unbornInitials > 0) {
    DHMap<Clause*, TracedClauseInfo*>::Iterator it(_clInfo);
    while (it.hasNext()) {
      Clause* cl;
      TracedClauseInfo* info;
      it.next(cl,info);

      if (info->isInital() && info->_state == NONE) {
        cout << info->_name << " " << cl->toString() << endl;
      }
    }
  }
}


void ProofTracer::init(const vstring& traceFileNames)
{
  CALL("ProofTracer::init");

  ScopedLet<unsigned> temporarilyResetUnitCounter(Unit::_lastNumber,0);

  // TODO: make this handle more then one trace file, i.e., start by splitting traceFileNames into pieces and calling getUnits more than once
  ParsedProof* pp = getParsedProof(traceFileNames); // deals with the file
  _tp = prepareTracedProof(pp);                     // creates clauses out of the clausal part of pp, connects the clauses by pointers and discards the rest
  _tp->init();                                      // set the counters for proper event watching
}

/**
 * Create a problem object.
 *
 * The new object takes ownership of the list @c units.
 */
Problem::Problem(UnitList* units)
: _units(0), _smtlibLogic(SMTLIBLogic::SMT_UNDEFINED) 
{
  CALL("Problem::Problem(UnitList*)");

  initValues();

  addUnits(units);
}

/**
 * Create a problem object.
 *
 * If @c copy is false, the new object takes ownership of the
 * clauses in the iterator.
 */
Problem::Problem(ClauseIterator clauses, bool copy)
: _units(0)
{
  CALL("Problem::Problem(ClauseIterator,bool)");

  initValues();

  UnitList* units = 0;
  while(clauses.hasNext()) {
    Clause* cl = clauses.next();
    if(copy) {
      cl = Clause::fromClause(cl);
    }
    UnitList::push(cl, units);
  }
  addUnits(units);

}

Problem::~Problem()
{
  CALL("Problem::~Problem");

  if(_property) { delete _property; }

  //TODO: decrease reference counter of clauses (but make sure there's no segfault...)

  UnitList::destroy(_units);
}

/**
 * Initialize values of information in the problem
 *
 * This function we have to share the initialisation code among different
 * constructors.
 */
void Problem::initValues()
{
  CALL("Problem::initValues");

  _hadIncompleteTransformation = false;
  _mayHaveEquality = true;
  _mayHaveFormulas = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
  _propertyValid = false;
  _property = 0;
}

/**
 * Add units into the problem. If the property object is valid, update it
 * so that it stays valid, otherwise invalidate the stored knowledge of the
 * problem.
 */
void Problem::addUnits(UnitList* newUnits)
{
  CALL("Problem::addUnits");

  UnitList::Iterator uit(newUnits);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      static_cast<Clause*>(u)->incRefCnt();
    }
  }
  _units = UnitList::concat(newUnits, _units);
  if(_propertyValid) {
    TimeCounter tc(TC_PROPERTY_EVALUATION);
    _property->add(newUnits);
    readDetailsFromProperty();
  }
  else {
    invalidateEverything();
  }
}

/**
 * Iterator going through the clauses in the problem.
 * When this function is called, problem can no longer
 * contain formulas.
 */
ClauseIterator Problem::clauseIterator() const
{
  CALL("Problem::clauseIterator");

  //we first call mayHaveFormulas(). if this returns false, we know there are
  //no formulas. otherwise we call hasFormulas() which may cause rescanning
  //the problem property
  ASS(!mayHaveFormulas() || !hasFormulas());
  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units())) );
}

/**
 * Creates a copy of this problem object.
 *
 * We do not use the copy constructor for this purpose, because copying
 * of problems is a rare operation and we want to avoid unnoticed bugs
 * coming from passing the Problem object as an argument by value rather
 * than by reference.
 */
Problem* Problem::copy(bool copyClauses)
{
  CALL("Problem::copy/1");

  Problem* res = new Problem();
  copyInto(*res, copyClauses);
  return res;
}

/**
 * Creates a copy of this problem object.
 *
 * We do not use the copy constructor for this purpose, because copying
 * of problems is a rare operation and we want to avoid unnoticed bugs
 * coming from passing the Problem object as an argument by value rather
 * than by reference.
 */
void Problem::copyInto(Problem& tgt, bool copyClauses)
{
  CALL("Problem::copy/2");

  tgt.setSMTLIBLogic(getSMTLIBLogic());

  if(copyClauses) {
    UnitList* newUnits = 0;
    UnitList::Iterator uit(units());
    while(uit.hasNext()) {
      Unit* u = uit.next();
      if(!u->isClause()) {
	UnitList::push(u, newUnits);
	continue;
      }
      Clause* cl = static_cast<Clause*>(u);
      Clause* newCl = Clause::fromClause(cl);
      UnitList::push(newCl, newUnits);
    }
    tgt.addUnits(UnitList::reverse(newUnits));
  }else {
    tgt.addUnits(UnitList::copy(units()));
  }
  if(hadIncompleteTransformation()) {
    tgt.reportIncompleteTransformation();
  }
  if(isPropertyUpToDate()) {
    //if we have an up-to-date property, we just copy it into the
    //copied object so we save ourselves scanning for the property
    //in the child
    tgt._propertyValid = true;
    tgt._property = new Property(*_property);
    tgt.readDetailsFromProperty();
  }

  //TODO copy the deleted maps
}

/**
 * Register a trivial predicate that has been removed from the problem
 *
 * Trivial predicates are the predicates whose all occurrences
 * can be assigned either true or false.
 *
 * This information may be used during model output
 */
void Problem::addTrivialPredicate(unsigned pred, bool assignment)
{
  CALL("Problem::addTrivialPredicate");

  ALWAYS(_trivialPredicates.insert(pred, assignment));
}

void Problem::addBDDVarMeaning(unsigned var, BDDMeaningSpec spec) {
  CALL("Problem::addBDDVarMeaning");
  ASS(!spec.first || spec.first->ground());

  ALWAYS(_bddVarSpecs.insert(var, spec));
}

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition)
{
  CALL("Problem::addEliminatedFunction");
  ASS(definition->isEquality());

  _deletedFunctions.insert(func,definition);
}

/**
 * Register a predicate that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedPredicate(unsigned pred, Unit* definition)
{
  CALL("Problem::addEliminatedPredicate");

  _deletedPredicates.insert(pred,definition);
}

/**
 * Register a predicate that has been partially eliminated i.e. <=> replaced by => 
 *
 * This information may be used during model output
 */
void Problem::addPartiallyEliminatedPredicate(unsigned pred, Unit* definition)
{
  CALL("Problem::addPurePredicateDefinition");

  _partiallyDeletedPredicates.insert(pred,definition);
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  CALL("Problem::refreshProperty");

  TimeCounter tc(TC_PROPERTY_EVALUATION);
  ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase, Statistics::PROPERTY_SCANNING);

  if(_property) {
    delete _property;
  }
  _propertyValid = true;
  _property = Property::scan(_units);
  ASS(_property);
  _property->setSMTLIBLogic(getSMTLIBLogic());
  readDetailsFromProperty();
}

/**
 * Read the locally stored information from the Property object
 */
void Problem::readDetailsFromProperty() const
{
  CALL("Problem::readDetailsFromProperty");

  _hasFormulas = _property->hasFormulas();
  _hasEquality = _property->equalityAtoms()!=0;
  _hasInterpretedOperations = _property->hasInterpretedOperations();
  _hasFOOL = _property->hasFOOL();
  _hasCombs = _property->hasCombs();
  _hasApp = _property->hasApp();
  _hasAppliedVar = _property->hasAppliedVar();
  _hasInterpretedEquality = _property->hasInterpretedEquality();
  _hasLogicalProxy = _property->hasLogicalProxy();
  _hasPolymorphicSym = _property->hasPolymorphicSym();
  _quantifiesOverPolymorphicVar = _property->quantifiesOverPolymorphicVar();
  _hasBoolVar = _property->hasBoolVar();

  _mayHaveFormulas = _hasFormulas.value();
  _mayHaveEquality = _hasEquality.value();
  _mayHaveFunctionDefinitions = _property->hasProp(Property::PR_HAS_FUNCTION_DEFINITIONS);
  _mayHaveInequalityResolvableWithDeletion = _property->hasProp(Property::PR_HAS_INEQUALITY_RESOLVABLE_WITH_DELETION);
  _mayHaveXEqualsY = _property->hasProp(Property::PR_HAS_X_EQUALS_Y);
}

/**
 * Invalidate all the information stored about the problem
 */
void Problem::invalidateEverything()
{
  CALL("Problem::invalidateEverything");

  invalidateProperty();
  _hasFormulas = MaybeBool::UNKNOWN;
  _hasEquality = MaybeBool::UNKNOWN;
  _hasInterpretedOperations = MaybeBool::UNKNOWN;
  _hasFOOL = MaybeBool::UNKNOWN;
  _hasInterpretedEquality = MaybeBool::UNKNOWN;
  _hasCombs = MaybeBool::UNKNOWN;
  _hasApp = MaybeBool::UNKNOWN;
  _hasAppliedVar = MaybeBool::UNKNOWN;

  _mayHaveFormulas = true;
  _mayHaveEquality = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
}

/**
 * Invalidate the information about problem that could have been
 * violated by removing some formulas or their parts
 */
void Problem::invalidateByRemoval()
{
  CALL("Problem::invalidateByRemoval");

  invalidateProperty();
  _hasFormulas.mightBecameFalse();
  _hasEquality.mightBecameFalse();
  _hasInterpretedOperations.mightBecameFalse();
  _hasFOOL.mightBecameFalse();
  _hasCombs.mightBecameFalse();
  _hasAppliedVar.mightBecameFalse();
  _hasLogicalProxy.mightBecameFalse();
  _hasPolymorphicSym.mightBecameFalse();
  _quantifiesOverPolymorphicVar.mightBecameFalse();
  _hasBoolVar.mightBecameFalse();
  _hasInterpretedEquality.mightBecameFalse();
}

/**
 * Return property corresponding to the current state of the problem
 */
Property* Problem::getProperty() const
{
  CALL("Problem::getProperty");

  if(!_propertyValid) {
    refreshProperty();
  }
  ASS(_property);

  return _property;
}


bool Problem::hasFormulas() const
{
  CALL("Problem::hasFormulas");

  if(!mayHaveFormulas()) { return false; }
  if(!_hasFormulas.known()) { refreshProperty(); }  
  ASS(_hasFormulas.known());
  return _hasFormulas.value();
}

bool Problem::hasEquality() const
{
  CALL("Problem::hasEquality");

  if(!mayHaveEquality()) { return false; }
  if(!_hasEquality.known()) { refreshProperty(); }
  return _hasEquality.value();
}

bool Problem::hasInterpretedOperations() const
{
  CALL("Problem::hasInterpretedOperations");

  if(!_hasInterpretedOperations.known()) { refreshProperty(); }
  return _hasInterpretedOperations.value();
}

bool Problem::hasInterpretedEquality() const
{
  CALL("Problem::hasInterpretedEquality");

  if(!_hasInterpretedEquality.known()) { refreshProperty(); }
  return _hasInterpretedEquality.value();
}

bool Problem::hasFOOL() const
{
  CALL("Problem::hasFOOL");

  if(!_hasFOOL.known()) { refreshProperty(); }
  return _hasFOOL.value();
}

bool Problem::hasCombs() const
{
  CALL("Problem::hasCombs");

  if(!_hasCombs.known()) { refreshProperty(); }
  return _hasCombs.value();
}


bool Problem::hasApp() const
{
  CALL("Problem::hasApp");

  if(!_hasApp.known()) { refreshProperty(); }
  return _hasApp.value();
}

bool Problem::hasAppliedVar() const
{
  CALL("Problem::hasAppliedVar");

  if(!_hasAppliedVar.known()) { refreshProperty(); }
  return _hasAppliedVar.value();
}

bool Problem::hasBoolVar() const
{
  CALL("Problem::hasBoolVar");

  if(!_hasBoolVar.known()) { refreshProperty(); }
  return _hasBoolVar.value();
}


bool Problem::hasLogicalProxy() const
{
  CALL("Problem::hasLogicalProxy");

  if(!_hasLogicalProxy.known()) { refreshProperty(); }
  return _hasLogicalProxy.value();
}

bool Problem::hasPolymorphicSym() const
{
  CALL("Problem::hasPolymorphicSym");

  if(!_hasPolymorphicSym.known()) { refreshProperty(); }
  return _hasPolymorphicSym.value();
}

bool Problem::quantifiesOverPolymorphicVar() const
{
  CALL(" Problem::quantifiesOverPolymorphicVar");

  if(!_quantifiesOverPolymorphicVar.known()) { refreshProperty(); }
  return _quantifiesOverPolymorphicVar.value();
}

///////////////////////
// utility functions
//

/**
 * Put predicate numbers present in the problem into @c acc
 *
 * The numbers added to acc are not unique.
 *
 */
void Problem::collectPredicates(Stack<unsigned>& acc) const
{
  CALL("Problem::collectPredicates");

  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    u->collectPredicates(acc);
  }
}

#if VDEBUG
///////////////////////
// debugging
//
void Problem::assertValid()
{
  CALL("Problem::assertValid");

  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASSERT_VALID(*u);
  }
}
#endif
