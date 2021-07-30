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
#include "Debug/TimeProfiling.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Shell/Property.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/FunctionDefinitionHandler.hpp"

#include "Clause.hpp"
#include "Term.hpp"

#include "Kernel/Inference.hpp"

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
using namespace std;

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
  //cout << "Init " << cl->toString() << endl;

  Clause* match = _tp->findVariant(cl);
  if (match != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(match);

    cout << "Init " << cl->toString() << endl;
    cout << " matched " << info->_name << endl;
    _tp->initalBorn();

    /*
    for (unsigned i = 0; i < info->_children.size(); i++) {
      Clause* ch = info->_children[i];
      TracedClauseInfo* ch_info = _tp->getClauseInfo(ch);
      cout << " would notify child " << ch_info->_name << endl;
      cout << " ik: " << ch_info->_ik << endl;
      cout << " pc: " << ch_info->_parents.size() << endl;
    }
    */
  }
}

void ProofTracer::onInputFinished()
{
  cout << "Input finished" << endl;

  _tp->onInputFinished();
}

void ProofTracer::onNewClause(Clause* cl)
{
  Clause* match = _tp->findVariant(cl);
  if (match != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(match);
    cout << "New " << cl->toString() << endl;
    cout << " matched " << info->_name << endl;
    if (_tp->_expecting.find(match)) {
      _tp->_expecting.remove(match);
      cout << "Was expected! Still expecting "; _tp->listExpecteds();
    }

    if (info->_stalkees.size()) {
      cout << "Already stalking" << endl;
    } else {
      // at the moment of assigning a (first) stalkee, we decrease the counter of children to find the expected ones...
      for (unsigned i = 0; i < info->_children.size(); i++) {
        Clause* ch = info->_children[i];
        TracedClauseInfo* ch_info = _tp->getClauseInfo(ch);
        ch_info->_numAwokenParents++;
        if (ch_info->_numAwokenParents == ch_info->_parents.size()) {
          cout << "Newly expecting " << ch_info->_name << " in addition to "; _tp->listExpecteds();
          _tp->_expecting.insert(ch);
        }
      }
    }

    // in any case, add this guy to the stalkees
    info->_stalkees.push(cl);
    _tp->listExpectedsDetails();

    cout << endl;
  }
}

void ProofTracer::onActivation(Clause* cl)
{
  Clause* _lastActivationMatch = _tp->findVariant(cl);
  if (_lastActivationMatch != 0) {
    TracedClauseInfo* info = _tp->getClauseInfo(_lastActivationMatch);

    cout << "Activate " << cl->toString() << endl;
    cout << " matched " << info->_name << endl;

  }
}

void ProofTracer::onActivationFinished(Clause* cl)
{
  if (_lastActivationMatch) {
    ASS_EQ(_lastActivationMatch,_tp->findVariant(cl));

    TracedClauseInfo* info = _tp->getClauseInfo(_lastActivationMatch);
  }
}



ProofTracer::ParsedProof* ProofTracer::getParsedProof(const vstring& proofFileName)
{
  ParsedProof* resultProof = new ParsedProof();

  istream* input;
  {
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
    vstring inf = "input";
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
      inf = irec->name;

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

    tp->regNewClause(cl,uname,inf,ik);
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
  cout << "proof size: " << _clInfo.size() << endl << endl;
  // cout << "_unbornInitials: " << _unbornInitials << endl;
}

void ProofTracer::TracedProof::onInputFinished()
{
  if (_unbornInitials > 0) {
    cout << "_unbornInitials: " << _unbornInitials << endl;
    DHMap<Clause*, TracedClauseInfo*>::Iterator it(_clInfo);
    while (it.hasNext()) {
      Clause* cl;
      TracedClauseInfo* info;
      it.next(cl,info);

      if (info->isInital() && info->_stalkees.size() == 0) {
        cout << info->_name << " " << cl->toString() << endl;
      }
    }
  } else {
    cout << "All initials recognized!" << endl << endl;
  }
}

void ProofTracer::TracedProof::listExpecteds()
{
  // just print all on one line
  DHSet<Clause*>::Iterator it(_expecting);
  while(it.hasNext()) {
    TracedClauseInfo* info = _clInfo.get(it.next());
    cout << " " << info->_name;
  }
  cout << endl;
}

void ProofTracer::TracedProof::listExpectedsDetails()
{
  // list each expected's parents' stalkee's store! ;)

  DHSet<Clause*>::Iterator it(_expecting);
  while(it.hasNext()) {
    Clause* e = it.next();
    TracedClauseInfo* e_info = _clInfo.get(e);
    cout << "  E: " << e_info->_name << " IK: " << e_info->_ik << " " << e_info->_inf << " CL: " << e->toNiceString() << endl;
    for (unsigned i = 0; i < e_info->_parents.size(); i++) {
      TracedClauseInfo* p_info = _clInfo.get(e_info->_parents[i]);
      cout << "    p: " << p_info->_name << endl;
      for (unsigned j = 0; j < p_info->_stalkees.size(); j++) {
        cout << "      s: ";
        Clause* stalkee = p_info->_stalkees[j];

        switch(stalkee->store()) {
          case Clause::Store::PASSIVE:
            cout << "PASSIVE: ";
            break;
          case Clause::Store::ACTIVE:
            cout << "ACTIVE: ";
            break;
          case Clause::Store::UNPROCESSED:
            cout << "UNPROCESSED:";
            break;
          case Clause::Store::NONE:
            cout << "NONE: ";
            break;
          case Clause::Store::SELECTED:
            cout << "SELECTED: ";
            break;
        }
        cout << stalkee->toString() << endl;
      }
    }
  }
}

void ProofTracer::init(const vstring& traceFileNames)
{
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
: _units(0), _fnDefHandler(new FunctionDefinitionHandler()), _smtlibLogic(SMTLIBLogic::SMT_UNDEFINED), _property(0)
{
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
: _units(0), _fnDefHandler(new FunctionDefinitionHandler()), _property(0)
{
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
  // Don't delete the property as it is owned by Environment
}

/**
 * Initialize values of information in the problem
 *
 * This function we have to share the initialisation code among different
 * constructors.
 */
void Problem::initValues()
{
  _hadIncompleteTransformation = false;
  _mayHaveEquality = true;
  _mayHaveFormulas = true;
  _mayHaveFunctionDefinitions = true;
  _mayHaveInequalityResolvableWithDeletion = true;
  _mayHaveXEqualsY = true;
  _propertyValid = false;
}

/**
 * Add units into the problem. If the property object is valid, update it
 * so that it stays valid, otherwise invalidate the stored knowledge of the
 * problem.
 */
void Problem::addUnits(UnitList* newUnits)
{
  UnitList::Iterator uit(newUnits);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      static_cast<Clause*>(u)->incRefCnt();
    }
  }
  _units = UnitList::concat(newUnits, _units);
  if(_propertyValid) {
    TIME_TRACE(TimeTrace::PROPERTY_EVALUATION);
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
  //we first call mayHaveFormulas(). if this returns false, we know there are
  //no formulas. otherwise we call hasFormulas() which may cause rescanning
  //the problem property
  ASS(!mayHaveFormulas() || !hasFormulas());
  return pvi( iterTraits(UnitList::Iterator(units())).map([](Unit* u) { return (Clause*)u; }) );
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
    //warning: both objects contain a pointer to the same property.
    //after copying, the property should be treated as strictly read
    //only.
    tgt._property = _property;
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
  ALWAYS(_trivialPredicates.insert(pred, assignment));
}

/**
 * Register a function that has been eliminated from the problem
 *
 * This information may be used during model output
 */
void Problem::addEliminatedFunction(unsigned func, Literal* definition)
{
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
  _deletedPredicates.insert(pred,definition);
}

/**
 * Register a predicate that has been partially eliminated i.e. <=> replaced by =>
 *
 * This information may be used during model output
 */
void Problem::addPartiallyEliminatedPredicate(unsigned pred, Unit* definition)
{
  _partiallyDeletedPredicates.insert(pred,definition);
}

/**
 * Recalculate the property from the current set of formulas
 */
void Problem::refreshProperty() const
{
  TIME_TRACE(TimeTrace::PROPERTY_EVALUATION);
  ScopedLet<Statistics::ExecutionPhase> phaseLet(env.statistics->phase, Statistics::PROPERTY_SCANNING);

  auto oldProp = _property;
  _propertyValid = true;
  _property = Property::scan(_units);
  if(oldProp) {
    delete oldProp;
  }
  ASS(_property);
  _property->setSMTLIBLogic(getSMTLIBLogic());
  readDetailsFromProperty();
}

/**
 * Read the locally stored information from the Property object
 */
void Problem::readDetailsFromProperty() const
{
  _hasFormulas = _property->hasFormulas();
  _hasEquality = _property->equalityAtoms()!=0;
  _hasInterpretedOperations = _property->hasInterpretedOperations();
  _hasNumerals = _property->hasNumerals();
  _hasFOOL = _property->hasFOOL();
  _hasCombs = _property->hasCombs();
  _hasApp = _property->hasApp();
  _hasAppliedVar = _property->hasAppliedVar();
  _hasLogicalProxy = _property->hasLogicalProxy();
  _hasPolymorphicSym = _property->hasPolymorphicSym();
  _quantifiesOverPolymorphicVar = _property->quantifiesOverPolymorphicVar();
  _hasBoolVar = _property->hasBoolVar();
  _higherOrder = _property->higherOrder();
  _hasNonDefaultSorts = _property->hasNonDefaultSorts();

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
  invalidateProperty();
  _hasFormulas = MaybeBool::Unknown;
  _hasEquality = MaybeBool::Unknown;
  _hasInterpretedOperations = MaybeBool::Unknown;
  _hasNumerals = MaybeBool::Unknown;
  _hasFOOL = MaybeBool::Unknown;
  _hasCombs = MaybeBool::Unknown;
  _hasApp = MaybeBool::Unknown;
  _hasAppliedVar = MaybeBool::Unknown;

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
  invalidateProperty();
  _hasFormulas.mightBecameFalse();
  _hasEquality.mightBecameFalse();
  _hasInterpretedOperations.mightBecameFalse();
  _hasNumerals.mightBecameFalse();
  _hasFOOL.mightBecameFalse();
  _hasCombs.mightBecameFalse();
  _hasAppliedVar.mightBecameFalse();
  _hasLogicalProxy.mightBecameFalse();
  _hasPolymorphicSym.mightBecameFalse();
  _quantifiesOverPolymorphicVar.mightBecameFalse();
  _hasBoolVar.mightBecameFalse();
}

/**
 * Return property corresponding to the current state of the problem
 */
Property* Problem::getProperty() const
{
  if(!_propertyValid) {
    refreshProperty();
  }
  ASS(_property);

  return _property;
}


bool Problem::hasFormulas() const
{
  if(!mayHaveFormulas()) { return false; }
  if(!_hasFormulas.known()) { refreshProperty(); }
  ASS(_hasFormulas.known());
  return _hasFormulas.value();
}

bool Problem::hasEquality() const
{
  if(!mayHaveEquality()) { return false; }
  if(!_hasEquality.known()) { refreshProperty(); }
  return _hasEquality.value();
}

bool Problem::hasInterpretedOperations() const
{
  if(!_hasInterpretedOperations.known()) { refreshProperty(); }
  return _hasInterpretedOperations.value();
}

bool Problem::hasNumerals() const
{
  if(!_hasNumerals.known()) { refreshProperty(); }
  return _hasNumerals.value();
}

bool Problem::hasFOOL() const
{
  if(!_hasFOOL.known()) { refreshProperty(); }
  return _hasFOOL.value();
}

bool Problem::hasCombs() const
{
  if(!_hasCombs.known()) { refreshProperty(); }
  return _hasCombs.value();
}


bool Problem::hasApp() const
{
  if(!_hasApp.known()) { refreshProperty(); }
  return _hasApp.value();
}

bool Problem::hasAppliedVar() const
{
  if(!_hasAppliedVar.known()) { refreshProperty(); }
  return _hasAppliedVar.value();
}

bool Problem::hasBoolVar() const
{
  if(!_hasBoolVar.known()) { refreshProperty(); }
  return _hasBoolVar.value();
}


bool Problem::hasLogicalProxy() const
{
  if(!_hasLogicalProxy.known()) { refreshProperty(); }
  return _hasLogicalProxy.value();
}

bool Problem::hasPolymorphicSym() const
{
  if(!_hasPolymorphicSym.known()) { refreshProperty(); }
  return _hasPolymorphicSym.value();
}

bool Problem::quantifiesOverPolymorphicVar() const
{
  if(!_quantifiesOverPolymorphicVar.known()) { refreshProperty(); }
  return _quantifiesOverPolymorphicVar.value();
}

bool Problem::isHigherOrder() const
{
  if(!_higherOrder.known()) { refreshProperty(); }
  return _higherOrder.value();
}

bool Problem::hasNonDefaultSorts() const
{
  if(!_hasNonDefaultSorts.known()) { refreshProperty(); }
  return _hasNonDefaultSorts.value();
}

#if VDEBUG
///////////////////////
// debugging
//
void Problem::assertValid()
{
  UnitList::Iterator uit(units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASSERT_VALID(*u);
  }
}
#endif
