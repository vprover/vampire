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
 * @file Api/Problem.cpp
 * Implements class Problem.
 */

#include "Problem.hpp"

#include "Helper_Internal.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/OptionsReader.hpp"
#include "Lib/ScopedLet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/AIGCompressor.hpp"
#include "Shell/AIGDefinitionIntroducer.hpp"
#include "Shell/AIGConditionalRewriter.hpp"
#include "Shell/AIGInliner.hpp"
#include "Shell/CNF.hpp"
#include "Shell/EPRInlining.hpp"
#include "Shell/EPRSkolem.hpp"
#include "Shell/EqualityPropagator.hpp"
#include "Shell/EquivalenceDiscoverer.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/LispParser.hpp"
#include "Shell/Naming.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/PDInliner.hpp"
#include "Shell/PDMerger.hpp"
#include "Shell/PredicateDefinition.hpp"
#include "Shell/PredicateIndexIntroducer.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/SimplifyProver.hpp"
#include "Shell/SineUtils.hpp"
#include "Shell/FOOLElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/VarManager.hpp"

#include "Parse/TPTP.hpp"

namespace Api {

using namespace Lib;

Problem::PreprocessingOptions::OptDataStore::OptDataStore()
{
  CALL("Problem::PreprocessingOptions::ARRStore::ARRStore()");

  lhs = new Stack<Formula>();
  posRhs = new Stack<Formula>();
  negRhs = new Stack<Formula>();
  dblRhs = new Stack<Formula>();
  pedSet1 = new Stack<Kernel::Literal*>();
  pedSet2 = new Stack<Kernel::Literal*>();
}

Problem::PreprocessingOptions::OptDataStore::OptDataStore(const OptDataStore& o)
{
  CALL("Problem::PreprocessingOptions::ARRStore::ARRStore(const ARRStore&)");

  lhs = new Stack<Formula>(*o.lhs);
  posRhs = new Stack<Formula>(*o.posRhs);
  negRhs = new Stack<Formula>(*o.negRhs);
  dblRhs = new Stack<Formula>(*o.dblRhs);
  pedSet1 = new Stack<Kernel::Literal*>(*o.pedSet1);
  pedSet2 = new Stack<Kernel::Literal*>(*o.pedSet2);
}

Problem::PreprocessingOptions::OptDataStore& Problem::PreprocessingOptions::OptDataStore::operator=(const OptDataStore& o)
{
  CALL("Problem::PreprocessingOptions::ARRStore::operator=");

  *lhs = *o.lhs;
  *posRhs = *o.posRhs;
  *negRhs = *o.negRhs;
  *dblRhs = *o.dblRhs;
  *pedSet1 = *o.pedSet1;
  *pedSet2 = *o.pedSet2;
  return *this;
}

Problem::PreprocessingOptions::OptDataStore::~OptDataStore()
{
  CALL("Problem::PreprocessingOptions::ARRStore::~ARRStore");

  delete lhs;
  delete posRhs;
  delete negRhs;
  delete dblRhs;
  delete pedSet1;
  delete pedSet2;
}

void Problem::PreprocessingOptions::OptDataStore::setDefaults()
{
  CALL("Problem::PreprocessingOptions::OptDataStore::setDefaults");

  lhs->reset();
  posRhs->reset();
  negRhs->reset();
  dblRhs->reset();
  pedSet1->reset();
  pedSet2->reset();
}


Problem::PreprocessingOptions::PreprocessingOptions()
{
  CALL("Problem::PreprocessingOptions::PreprocessingOptions/0");

  setDefaults();
}

Problem::PreprocessingOptions::PreprocessingOptions(vstring spec)
{
  CALL("Problem::PreprocessingOptions::PreprocessingOptions/1");

  setDefaults();

  OptionsReader optReader;
  prepareOptionsReader(optReader);
  if(!optReader.readOptions(spec)) {
    throw ApiException("Invalid preprocessing specification string: \""+spec+"\"");
  }
}

void Problem::PreprocessingOptions::prepareOptionsReader(OptionsReader& rdr)
{
  CALL("Problem::PreprocessingOptions::prepareOptionsReader");

  EnumReader<PreprocessingMode> enumPreprMode;
  enumPreprMode.addVal("selection_only", PM_SELECTION_ONLY);
  enumPreprMode.addVal("early_preprocessing", PM_EARLY_PREPROCESSING);
  enumPreprMode.addVal("skolemize", PM_SKOLEMIZE);
  enumPreprMode.addVal("clausify", PM_CLAUSIFY);

  EnumReader<InliningMode> enumInliningMode;
  enumInliningMode.addVal("off", INL_OFF);
  enumInliningMode.addVal("on", INL_ON);
  enumInliningMode.addVal("axioms_only", INL_AXIOMS_ONLY);
  enumInliningMode.addVal("epr_restoring", INL_EPR_RESTORING);
  enumInliningMode.addVal("predicate_equivalences_only", INL_PREDICATE_EQUIVALENCES_ONLY);
  enumInliningMode.addVal("no_discovered_defs", INL_NO_DISCOVERED_DEFS);
  enumInliningMode.addVal("non_growing", INL_NON_GROWING);

  EnumReader<EquivalenceDiscovery> enumEquivalenceDiscovery;
  enumEquivalenceDiscovery.addVal("none", ED_NONE);
  enumEquivalenceDiscovery.addVal("predicate_equivalences", ED_PREDICATE_EQUIVALENCES);
  enumEquivalenceDiscovery.addVal("predicate_definitions", ED_PREDICATE_DEFINITIONS);
  enumEquivalenceDiscovery.addVal("atom_equivalences", ED_ATOM_EQUIVALENCES);
  enumEquivalenceDiscovery.addVal("formula_equivalences", ED_FORMULA_EQUIVALENCES);

  EnumReader<FixpointCheck> enumFixpointCheck;
  enumFixpointCheck.addVal("none", FC_NONE);
  enumFixpointCheck.addVal("formula_count", FC_FORMULA_COUNT);

  rdr.registerEnumOption(&mode, enumPreprMode, "preprocessing_mode", "m");
  rdr.registerIntOption(&namingThreshold, "naming_treshold", "nt");
  rdr.registerBoolOption(&preserveEpr, "preserve_epr", "pe");
  rdr.registerEnumOption(&predicateDefinitionInlining, enumInliningMode, "predicate_definition_inlining", "pdi");
  rdr.registerBoolOption(&unusedPredicateDefinitionRemoval, "unused_predicate_definition_removal", "updr");
  rdr.registerBoolOption(&sineSelection, "sine_selection", "ss");
  rdr.registerFloatOption(&sineTolerance, "sine_tolerance", "st");
  rdr.registerUnsignedOption(&sineDepthLimit, "sine_depth_limit", "sdl");
  rdr.registerBoolOption(&variableEqualityPropagation, "variable_equality_propagation", "vep");
  rdr.registerBoolOption(&eprSkolemization, "epr_skolemization", "es");
  rdr.registerBoolOption(&predicateDefinitionMerging, "predicate_definition_merging", "pdm");
  rdr.registerBoolOption(&predicateIndexIntroduction, "predicate_index_introduction", "pii");
  rdr.registerBoolOption(&flatteningTopLevelConjunctions, "flattening_top_level_conjunctions", "ftlc");
  rdr.registerEnumOption(&equivalenceDiscovery, enumEquivalenceDiscovery, "equivalence_discovery", "ed");
  rdr.registerBoolOption(&equivalenceDiscoveryRetrievePremises, "equivalence_discovery_retrieve_premises", "edrp");
  rdr.registerUnsignedOption(&equivalenceDiscoverySatConflictLimit, "equivalence_discovery_sat_conflict_limit", "edscl");
  rdr.registerBoolOption(&equivalenceDiscoveryAddImplications, "equivalence_discovery_add_implications", "edai");
  rdr.registerBoolOption(&equivalenceDiscoveryRandomSimulation, "equivalence_discovery_random_simulation", "edrs");
  rdr.registerBoolOption(&aigInlining, "aig_inlining", "ai");
  rdr.registerBoolOption(&aigBddSweeping, "aig_bdd_sweeping", "abs");
  rdr.registerUnsignedOption(&aigBddSweepingMaximumBddAtomCount, "aig_bdd_sweeping_maximum_bdd_atom_count", "absmbac");
  rdr.registerBoolOption(&aigDefinitionIntroduction, "aig_definition_introduction", "adi");
  rdr.registerBoolOption(&aigConditionalRewriting, "aig_conditional_rewriting", "acr");

  rdr.registerUnsignedOption(&repetitionCount, "repetition_count", "rc");
  rdr.registerEnumOption(&repetitionEarlyTermination, enumFixpointCheck, "repetition_early_termination", "ret");
}

void Problem::PreprocessingOptions::setDefaults()
{
  CALL("Problem::PreprocessingOptions::setDefaults");

  mode = PM_CLAUSIFY;
  namingThreshold = 8;
  preserveEpr = false;
  predicateDefinitionInlining = INL_OFF;
  unusedPredicateDefinitionRemoval = true;
  showNonConstantSkolemFunctionTrace = false;
  sineSelection = false;
  sineTolerance = 1.0f;
  sineDepthLimit = 0;
  variableEqualityPropagation = false;
  eprSkolemization = false;
  predicateDefinitionMerging = false;
  predicateIndexIntroduction = false;
  flatteningTopLevelConjunctions = false;
  equivalenceDiscovery = ED_NONE;
  equivalenceDiscoveryRetrievePremises = true;
  equivalenceDiscoverySatConflictLimit = UINT_MAX;
  equivalenceDiscoveryAddImplications = false;
  equivalenceDiscoveryRandomSimulation = true;
  aigInlining = false;
  aigBddSweeping = false;
  aigBddSweepingMaximumBddAtomCount = 16;
  aigDefinitionIntroduction = false;
  aigConditionalRewriting = false;
  repetitionCount = 1;
  repetitionEarlyTermination = FC_NONE;

  _predicateEquivalenceDiscoveryRestricted = false;
  _ods.setDefaults();
}

void Problem::PreprocessingOptions::printOptionValues(ostream& out)
{
  CALL("Problem::PreprocessingOptions::printOptionValues");

  OptionsReader curRdr;
  prepareOptionsReader(curRdr);

  OptionsReader defRdr;
  PreprocessingOptions def;
  def.prepareOptionsReader(defRdr);

  curRdr.printOptionValues(out, &defRdr, "option value ");
}

void Problem::PreprocessingOptions::addAsymmetricRewritingRule(Formula lhs,
    Formula posRhs, Formula negRhs, Formula dblRhs)
{
  CALL("Problem::PreprocessingOptions::addAsymmetricRewritingRule");
  ASS_EQ(_ods.lhs->size(),_ods.posRhs->size());
  ASS_EQ(_ods.lhs->size(),_ods.negRhs->size());
  ASS_EQ(_ods.lhs->size(),_ods.dblRhs->size());

  _ods.lhs->push(lhs);
  _ods.posRhs->push(posRhs);
  _ods.negRhs->push(negRhs);
  _ods.dblRhs->push(dblRhs);
}

void Problem::PreprocessingOptions::importAssymmetricRulesFrom(const PreprocessingOptions& src)
{
  CALL("Problem::PreprocessingOptions::importAssymmetricRulesFrom");

  _ods.lhs = src._ods.lhs;
  _ods.posRhs = src._ods.posRhs;
  _ods.negRhs = src._ods.negRhs;
  _ods.dblRhs = src._ods.dblRhs;
}

/**
 * Functor that extracts atoms from Api formulas that are aither atoms or negations of atoms.
 */
struct Problem::PreprocessingOptions::Atom2LitFn
{
  Kernel::Literal* operator()(Formula f) {
    CALL("Problem::PreprocessingOptions::Atom2LitFn::operator()");

    Kernel::Formula* form = f.form;
    while(form->connective()==Kernel::NOT) {
      form = form->uarg();
    }
    if(form->connective()!=Kernel::LITERAL) {
      throw ApiException("Formulas passed to PreprocessingOptions::restrictPredicateEquivalenceDiscovery must be atoms or negations of atoms");
    }
    return form->literal();
  }
};

void Problem::PreprocessingOptions::restrictPredicateEquivalenceDiscovery(size_t set1Sz, Formula* set1,
    size_t set2Sz, Formula* set2)
{
  CALL("Problem::PreprocessingOptions::restrictPredicateEquivalenceDiscovery");

  _predicateEquivalenceDiscoveryRestricted = true;
  _ods.pedSet1->reset();
  _ods.pedSet1->loadFromIterator(getMappingIterator(getArrayishObjectIterator(set1, set1Sz),Atom2LitFn()));
  _ods.pedSet2->reset();
  _ods.pedSet2->loadFromIterator(getMappingIterator(getArrayishObjectIterator(set2, set2Sz),Atom2LitFn()));
}

void Problem::PreprocessingOptions::validate() const
{
  CALL("Problem::PreprocessingOptions::validate");

  if(namingThreshold>32767 || namingThreshold<0) {
    throw new ApiException("namingThreshold must be in the range [0,32767]");
  }

  if(sineSelection && (sineTolerance<1.0f && sineTolerance!=-1.0f)) {
    throw new ApiException("sineTolerance must be greater than or equal to 1 or equal to -1");
  }
}

typedef List<AnnotatedFormula> AFList;

class Problem::PData
{
public:
  CLASS_NAME(Problem::PData);
  USE_ALLOCATOR(Problem::PData);
  
  PData() : _size(0), _forms(0), _refCnt(0)
  {
  }
  ~PData()
  {
    AFList::destroy(_forms);
  }

  void incRef() { _refCnt++; }
  void decRef()
  {
    ASS_G(_refCnt,0);
    _refCnt--;
    if(!_refCnt) {
      delete this;
    }
  }

  void cloneInto(PData* obj)
  {
    CALL("Problem::PData::cloneInto");
    ASS_EQ(obj->_forms, 0);

    obj->_forms = AFList::copy(_forms);
  }

  void addFormula(AnnotatedFormula f)
  {
    CALL("Problem::PData::addFormula");

    _size++;
    AFList::push(f, _forms);
  }

  size_t size() { return _size; }

  AFList*& forms() { return _forms; }

  /** Problem must be non-empty */
  ApiHelper getApiHelper() {
    CALL("Problem::PData::getApiHelper");
    ASS_G(size(),0);
    return _forms->head()._aux;
  }

  DefaultHelperCore* getCore() {
    CALL("Problem::PData::getCore");
    if(size()==0) { return 0; }
    return *getApiHelper();
  }

private:
  size_t _size;
  AFList* _forms;
  unsigned _refCnt;
};


Problem::Problem()
{
  CALL("Problem::Problem");

  _data=new PData;
  _data->incRef();
}

Problem::Problem(const Problem& p)
{
  CALL("Problem::Problem(const Problem&)");

  _data=const_cast<PData*>(p._data);
  _data->incRef();
}

Problem& Problem::operator=(const Problem& p)
{
  CALL("Problem::operator =");

  PData* oldData=_data;

  _data=const_cast<PData*>(p._data);

  _data->incRef();
  oldData->decRef();

  return *this;
}

Problem::~Problem()
{
  CALL("Problem::~Problem");

  _data->decRef();
}

Problem Problem::clone()
{
  CALL("Problem::clone");

  Problem res;
  _data->cloneInto(res._data);
  return res;
}

void Problem::addFormula(AnnotatedFormula f)
{
  CALL("Problem::addFormula");

  _data->addFormula(f);
}

size_t Problem::size()
{
  CALL("Problem::size");

  return _data->size();
}

bool Problem::empty()
{
  CALL("Problem::empty");

  return size()==0;
}



///////////////////////////////////////
// Parsing

void Problem::addFromStream(istream& s, vstring includeDirectory, bool simplifySyntax)
{
  CALL("Problem::addFromStream");

  using namespace Shell;

  vstring originalInclude=env.options->include();
  env.options->setInclude(includeDirectory);

  Kernel::UnitList* units;
  if(simplifySyntax) {
    LispLexer lexer(s);
    LispParser parser(lexer);
    LispParser::Expression* expr = parser.parse();
    SimplifyProver simplify;
    units = simplify.units(expr);
  }
  else { 
    units = Parse::TPTP::parse(s);
  }

  env.options->setInclude(originalInclude);
  while(units) {
    Kernel::Unit* u=Kernel::UnitList::pop(units);
    addFormula(AnnotatedFormula(u));
  }
}


///////////////////////////////////////
// Clausification

class Problem::ProblemTransformer
{
public:
  virtual ~ProblemTransformer() {}

  Problem transform(Problem p)
  {
    CALL("ProblemTransformer::transform(Problem)");

    VarManager::VarFactory* oldFactory = VarManager::varNamePreservingFactory();

    if(p.size()>0) {
      AnnotatedFormulaIterator fit=p.formulas();
      ALWAYS(fit.hasNext());
      AnnotatedFormula f=fit.next();

      _varFactory = f._aux->getVarFactory();
      VarManager::setVarNamePreserving(_varFactory);
    }

    Problem res;
    _res = &res;

    transformImpl(p);

    VarManager::setVarNamePreserving(oldFactory);
    _res = 0;
    return res;
  }

protected:
  ProblemTransformer() :
    _transforming(false), _res(0) {}

  /**
   * Transform @c unit and call @c addUnit() on the results of the transformation.
   */
  virtual void transformImpl(Kernel::Unit* unit) = 0;

  virtual void transformImpl(Problem p)
  {
    CALL("ProblemTransformer::transformImpl(Problem)");

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  /**
   * To be called by transformImpl(Problem p)
   */
  void transform(AnnotatedFormula f)
  {
    CALL("Problem::ProblemTransformer::transform(AnnotatedFormula)");
    ASS(!_transforming);
    ASS(_defs.isEmpty());

    _transforming = true;
    if(OutputOptions::assignFormulaNames()) {
      _origName = f.name();
    }
    _origUnit = f;
    _origAF = f;
    if(_varFactory!=f._aux->getVarFactory()) {
      throw ApiException("Transforming problem that contains formulas from diferent FormulaBuilder objects.");
    }

    _transformingDef = false;
    transformImpl(f);

    _transformingDef = true;
    while(_defs.isNonEmpty()) {
      transformImpl(_defs.pop_front());
    }

    _transforming = false;
  }

  void addUnit(Kernel::Unit* unit)
  {
    CALL("Problem::ProblemTransformer::addUnit");
    ASS(unit);

    AnnotatedFormula af = AnnotatedFormula(unit, _origAF._aux);
    _res->addFormula(af);
    if(unit==_origUnit) {
      //if added formula is the original one, we don't assign name to it
      return;
    }

    vstring unitName;
    //we don't worry about making the names unique, that's the business of
    //the AnnotatedFormula::assignName() function
    if(_transformingDef) {
      unitName="def";
    }
    else {
      unitName=_origName;
    }
    AnnotatedFormula::assignName(af, unitName);
  }

  void handleDefs(Kernel::UnitList*& defLst)
  {
    CALL("Problem::ProblemTransformer::addUnit");

    while(defLst) {
      _defs.push_back(Kernel::UnitList::pop(defLst));
    }
  }

  VarManager::VarFactory* _varFactory;

  bool _transforming;
  bool _transformingDef;
  vstring _origName;
  Kernel::Unit* _origUnit;
  AnnotatedFormula _origAF;

  Deque<Kernel::Unit*> _defs;

  Problem* _res;
};

class Problem::Preprocessor1 : public ProblemTransformer
{
protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::Preprocessor1::transformImpl");

    using namespace Shell;

    if(unit->isClause()) {
      addUnit(unit);
      return;
    }

    Kernel::FormulaUnit* fu = static_cast<Kernel::FormulaUnit*>(unit);
    Kernel::UnitList* newDefs=0;
    fu = FOOLElimination().apply(fu, newDefs);
    handleDefs(newDefs);


    fu = Rectify::rectify(fu);
    fu = SimplifyFalseTrue::simplify(fu);
    fu = Flattening::flatten(fu);

    addUnit(fu);
  }
};

class Problem::VariableEqualityPropagator : public ProblemTransformer
{
public:
  VariableEqualityPropagator() : _eqProp() {}
protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::VariableEqualityPropagator::transformImpl");

    addUnit(_eqProp.apply(unit));
  }
  EqualityPropagator _eqProp;
};

class Problem::BDDSweeper : public ProblemTransformer
{
public:
  BDDSweeper(unsigned maxBddVarCnt=16) : _act(maxBddVarCnt) {}
protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::BDDSweeper::transformImpl");

    Kernel::Unit* res;
    if(!_act.apply(unit, res)) {
      addUnit(unit);
    }
    else if(res) {
      addUnit(res);
    }
  }

  Shell::AIGCompressingTransformer _act;
};


class Problem::AIGInliner : public ProblemTransformer
{
public:
  AIGInliner()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::BDDSweeper::transformImpl(Problem)");

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _aii.scan(units);
    Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::BDDSweeper::transformImpl");

    Unit* res;
    if(!_aii.apply(unit, res)) {
      addUnit(unit);
    }
    else if(res) {
      addUnit(res);
    }
  }

  Shell::AIGInliner _aii;
};

class Problem::AIGDefinitionIntroducer : public ProblemTransformer
{
public:
  AIGDefinitionIntroducer()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::AIGDefinitionIntroducer::transformImpl(Problem)");

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _adi.scan(units);
    Kernel::UnitList::units->destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }

    UnitList* eqs = _adi.getIntroducedFormulas();

    while(eqs) {
      Kernel::Unit* u = Kernel::UnitList::pop(eqs);
      AnnotatedFormula af(u, p._data->getApiHelper());
      AnnotatedFormula::assignName(af, "def");
      _res->addFormula(af);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::AIGDefinitionIntroducer::transformImpl");

    Unit* res;
    if(!_adi.apply(unit, res)) {
      addUnit(unit);
    }
    else if(res) {
      addUnit(res);
    }
  }

  Shell::AIGDefinitionIntroducer _adi;
};

class Problem::AIGConditionalRewriter
{
public:
  Problem transform(Problem p)
  {
    CALL("AIGConditionalRewriter::transform");

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }

    Shell::AIGConditionalRewriter acr;
    acr.apply(units);

    Problem res;

    if(!units) {
      return res;
    }

    while(units) {
      Kernel::Unit* u = Kernel::UnitList::pop(units);
      AnnotatedFormula af(u, p._data->getApiHelper());
      res.addFormula(af);
    }
    return res;
  }
};

class Problem::PredicateIndexIntroducer : public ProblemTransformer
{
public:
  PredicateIndexIntroducer()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::PredicateIndexIntroducer::transformImpl(Problem)");

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _pii.scan(units);
    Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::PredicateIndexIntroducer::transformImpl");

    Unit* res;
    if(!_pii.apply(unit, res)) {
      addUnit(unit);
    }
    else if(res) {
      addUnit(res);
    }
  }

  Shell::PredicateIndexIntroducer _pii;
};

class Problem::TopLevelFlattener : public ProblemTransformer
{
protected:
  virtual void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl");

    if(unit->isClause()) {
      addUnit(unit);
      return;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(unit);
    static Stack<FormulaUnit*> acc;
    acc.reset();

    if(!_flt.apply(fu, acc)) {
      addUnit(unit);
      return;
    }
    while(acc.isNonEmpty()) {
      addUnit(acc.pop());
    }
  }

  Shell::TopLevelFlatten _flt;
};


class Problem::PredicateDefinitionMerger : public ProblemTransformer
{
public:
  PredicateDefinitionMerger()
      : _merger()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::PredicateDefinitionMerger::transformImpl(Problem)");

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _merger.scan(units);
    Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  virtual void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::PredicateDefinitionMerger::transformImpl");

    Kernel::Unit* res = _merger.apply(unit);
    if(res) {
      addUnit(res);
    }
  }

  Shell::PDMerger _merger;
};

class Problem::PredicateDefinitionInliner : public ProblemTransformer
{
public:
  PredicateDefinitionInliner(InliningMode mode)
      : _mode(mode), _pdInliner(mode==INL_AXIOMS_ONLY, mode==INL_NON_GROWING)
  {
    ASS_NEQ(mode, INL_OFF);
  }

  bool addAsymetricDefinition(Formula lhs, Formula posRhs, Formula negRhs, Formula dblRhs)
  {
    CALL("Problem::PredicateDefinitionInliner::addAsymetricDefinition");

    Kernel::Formula* lhsF = lhs;
    bool negate = false;
    while(lhsF->connective()==Kernel::NOT) {
      negate = !negate;
      lhsF = lhsF->uarg();
    }
    if(lhsF->connective()!=Kernel::LITERAL) {
      throw ApiException("LHS must be an atom");
    }
    Kernel::Literal* lhsLit = lhsF->literal();
    if(negate) {
      lhsLit = Kernel::Literal::complementaryLiteral(lhsLit);
    }

    Kernel::Formula* posForm = posRhs;
    Kernel::Formula* negForm = negRhs;
    Kernel::Formula* dblForm = dblRhs;

    return _pdInliner.addAsymetricDefinition(lhsLit, posForm, negForm, dblForm);
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::PredicateDefinitionInliner::transformImpl(Problem)");

    static DHSet<Kernel::Unit*> defs;
    defs.reset();

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] api: started def inlining" << std::endl;
      env.endOutput();
    }    

    AnnotatedFormulaIterator fit;
    if(_mode!=INL_NO_DISCOVERED_DEFS) {

      if(_mode==INL_NON_GROWING) {
	fit=p.formulas();
	while(fit.hasNext()) {
	  AnnotatedFormula f=fit.next();
	  _pdInliner.updatePredOccCounts(f.unit);
	}
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] api: non-growing counting finished" << std::endl;
    env.endOutput();
  }
      }

      fit=p.formulas();
      while(fit.hasNext()) {
	AnnotatedFormula f=fit.next();
	if(f.unit->isClause()) {
	  continue;
	}
	FormulaUnit* fu = static_cast<FormulaUnit*>(f.unit);
	if(_pdInliner.tryGetPredicateEquivalence(fu)) {
	  defs.insert(fu);
	}
      }
      if (env.options->showPreprocessing()) {
        env.beginOutput();
        env.out() << "[PP] api: predicate equivalence scan finished" << std::endl;
        env.endOutput();
      }

      if(_mode!=INL_PREDICATE_EQUIVALENCES_ONLY) {
	fit=p.formulas();
	while(fit.hasNext()) {
	  AnnotatedFormula f=fit.next();
	  if(f.unit->isClause() || defs.contains(f.unit)) {
	    continue;
	  }
	  FormulaUnit* fu = static_cast<FormulaUnit*>(f.unit);
	  if(_pdInliner.tryGetDef(fu)) {
	    defs.insert(fu);
	  }
	}
  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] api: other definition scan finished" << std::endl;
    env.endOutput();
  }
      }
    }

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      if(defs.contains(f.unit)) {
	continue; //we don't keep the definitions
      }
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::PredicateDefinitionInliner::transformImpl");

    Kernel::Unit* res = _pdInliner.apply(unit);
    if(res) {
      addUnit(res);
    }
  }

  InliningMode _mode;
  Shell::PDInliner _pdInliner;
};

class Problem::EPRRestoringInliner : public ProblemTransformer
{
public:
  EPRRestoringInliner()
      :  _eprInliner()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl(Problem)");

    p = PredicateDefinitionInliner(INL_PREDICATE_EQUIVALENCES_ONLY).transform(p);

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _eprInliner.scan(units);
    Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl");

    Kernel::Unit* res = _eprInliner.apply(unit);
    if(res) {
      addUnit(res);
    }
  }

  Shell::EPRInlining _eprInliner;
};

class Problem::ConstantSkolemizer : public ProblemTransformer
{
protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::ConstantSkolemizer::transformImpl");

    if(unit->isClause()) {
      addUnit(unit);
      return;
    }
    FormulaUnit* newUnit = EPRSkolem::constantSkolemize(static_cast<FormulaUnit*>(unit));
    addUnit(newUnit);
  }
};

class Problem::EPRSkolemizer : public ProblemTransformer
{
public:
  EPRSkolemizer()
      :  _eprSkolem()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl(Problem)");

    p = ConstantSkolemizer().transform(p);
    p = PredicateDefinitionInliner(INL_PREDICATE_EQUIVALENCES_ONLY).transform(p);

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _eprSkolem.scan(units);
    Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl");

    UnitList* res = 0;
    if(!_eprSkolem.apply(unit, res)) {
      addUnit(unit);
      return;
    }
    while(res) {
      Unit* ru = UnitList::pop(res);
      addUnit(ru);
    }
  }

  Shell::EPRSkolem _eprSkolem;
};


class Problem::UnusedPredicateDefinitionRemover : public ProblemTransformer
{
public:
  UnusedPredicateDefinitionRemover()
  : pd()
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::UnusedPredicateDefinitionRemover::transformImpl(Problem)");
    ASS(replacements.isEmpty()); //this function can be called only once per instance of this class

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    pd.collectReplacements(units, replacements);
        Kernel::UnitList::destroy(units);

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::UnusedPredicateDefinitionRemover::transformImpl");

    Kernel::Unit* v;
    if(!replacements.find(unit,v)) {
      addUnit(unit);
      return;
    }
    Kernel::Unit* tgt=v;
    while(replacements.find(v,tgt)) {
      v=tgt;
    }
    if(v && ( v->isClause() || static_cast<Kernel::FormulaUnit*>(v)->formula()->connective()!=TRUE ) ) {
      addUnit(v);
    }
  }

  Shell::PredicateDefinition pd;
  DHMap<Kernel::Unit*, Kernel::Unit*> replacements;
};

class Problem::PredicateEquivalenceDiscoverer
{
public:
  PredicateEquivalenceDiscoverer(EquivalenceDiscovery mode, unsigned satConflictCountLimit,
      bool doRandomSimulation, bool addImplications, bool retrievePremises,
      bool restricted, Stack<Kernel::Literal*>& restrSet1, Stack<Kernel::Literal*>& restrSet2)
  : _mode(mode), _satConflictCountLimit(satConflictCountLimit), _doRandomSimulation(doRandomSimulation),
    _addImplications(addImplications), _retrievePremises(retrievePremises),
    _restricted(restricted), _restrSet1(restrSet1), _restrSet2(restrSet2) {}

  Problem transform(Problem p)
  {
    CALL("PredicateEquivalenceDiscoverer::transform");

    if(p.empty()) {
      return p;
    }

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }

    bool formulaDiscovery = false;
    EquivalenceDiscoverer::CandidateRestriction restr;
    switch(_mode) {
    case ED_NONE:
      ASSERTION_VIOLATION;
      break;
    case ED_PREDICATE_EQUIVALENCES:
      restr = EquivalenceDiscoverer::CR_EQUIVALENCES;
      break;
    case ED_PREDICATE_DEFINITIONS:
      restr = EquivalenceDiscoverer::CR_DEFINITIONS;
      break;
    case ED_ATOM_EQUIVALENCES:
      restr = EquivalenceDiscoverer::CR_NONE;
      break;
    case ED_FORMULA_EQUIVALENCES:
      restr = EquivalenceDiscoverer::CR_NONE;
      formulaDiscovery = true;
      if(_restricted) {
	throw ApiException("cannot use atom restriction for formula equivalence discovery (ED_FORMULA_EQUIVALENCES)");
      }
      break;
    }

    Kernel::UnitList* eqs;

    EquivalenceDiscoverer ed(true, _satConflictCountLimit, restr, _addImplications, _doRandomSimulation,
	_retrievePremises);
    if(formulaDiscovery) {
      FormulaEquivalenceDiscoverer fed(ed);
      eqs = fed.getEquivalences(units);
    }
    else {
      if(_restricted) {
	ed.setRestrictedRange(pvi( Stack<Kernel::Literal*>::Iterator(_restrSet1) ),
	    pvi( Stack<Kernel::Literal*>::Iterator(_restrSet2)) );
      }
      eqs = ed.getEquivalences(units);
    }
        Kernel::UnitList::destroy(units);

    if(!eqs) { return p; }

    while(eqs) {
      Kernel::Unit* u = Kernel::UnitList::pop(eqs);
      AnnotatedFormula af(u, p._data->getApiHelper());
      AnnotatedFormula::assignName(af, "equiv");
      p.addFormula(af);
    }

    return PredicateDefinitionInliner(INL_NON_GROWING).transform(p);
  }

private:
  EquivalenceDiscovery _mode;
  unsigned _satConflictCountLimit;
  bool _doRandomSimulation;
  bool _addImplications;
  bool _retrievePremises;

  bool _restricted;
  Stack<Kernel::Literal*>& _restrSet1;
  Stack<Kernel::Literal*>& _restrSet2;
};



class Problem::SineSelector : public ProblemTransformer
{
public:
  SineSelector(float tolerance, unsigned depthLimit)
      : sine(false, tolerance, depthLimit) {}
protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::SineSelector::transformImpl(Problem)");
    ASS(selected.isEmpty()); //this function can be called only once per instance of this class

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }

    sine.perform(units);

    while(units) {
      Kernel::Unit* u = Kernel::UnitList::pop(units);
      selected.insert(u);
    }

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::SineSelector::transformImpl");

    if(selected.find(unit)) {
      addUnit(unit);
    }
  }

  Shell::SineSelector sine;
  DHSet<Kernel::Unit*> selected;
};

class Problem::Clausifier : public ProblemTransformer
{
public:
  Clausifier(int namingThreshold, bool preserveEpr, bool onlySkolemize) :
    namingThreshold(namingThreshold), preserveEpr(preserveEpr), onlySkolemize(onlySkolemize),
    naming(namingThreshold ? namingThreshold : 8, preserveEpr) {}

protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::Clausifier::transformImpl");

    using namespace Shell;

    if(unit->isClause()) {
      addUnit(unit);
      return;
    }

    Kernel::FormulaUnit* fu = static_cast<Kernel::FormulaUnit*>(unit);

    fu = NNF::ennf(fu);
    fu = Flattening::flatten(fu);

    if(!_transformingDef && namingThreshold) {
      Kernel::UnitList* newDefs=0;
      fu = naming.apply(fu,newDefs);
      handleDefs(newDefs);
    }

    fu = NNF::nnf(fu);
    fu = Flattening::flatten(fu);
    fu = Skolem::skolemise(fu);
    if(onlySkolemize) {
      addUnit(fu);
    }
    else {
      if(!_transformingDef && namingThreshold && preserveEpr) {
	Kernel::UnitList* newDefs=0;
	fu = naming.apply(fu,newDefs);
	handleDefs(newDefs);
      }

      cnf.clausify(fu,auxClauseStack);
      while (! auxClauseStack.isEmpty()) {
	Unit* cl = auxClauseStack.pop();
	addUnit(cl);
      }
    }
  }

  int namingThreshold;
  bool preserveEpr;
  bool onlySkolemize;

  Shell::CNF cnf;
  Stack<Kernel::Clause*> auxClauseStack;
  Shell::Naming naming;
};

Problem Problem::clausify(int namingThreshold, bool preserveEpr, InliningMode predicateDefinitionInlining,
    bool unusedPredicateDefinitionRemoval)
{
  CALL("Problem::clausify");

  PreprocessingOptions opts;
  opts.mode = PM_CLAUSIFY;
  opts.namingThreshold = namingThreshold;
  opts.preserveEpr = preserveEpr;
  opts.predicateDefinitionInlining = predicateDefinitionInlining;
  opts.unusedPredicateDefinitionRemoval = unusedPredicateDefinitionRemoval;

  return preprocess(opts);
}

Problem Problem::skolemize(int namingThreshold, bool preserveEpr, InliningMode predicateDefinitionInlining,
    bool unusedPredicateDefinitionRemoval)
{
  CALL("Problem::skolemize");

  PreprocessingOptions opts;
  opts.mode = PM_SKOLEMIZE;
  opts.namingThreshold = namingThreshold;
  opts.preserveEpr = preserveEpr;
  opts.predicateDefinitionInlining = predicateDefinitionInlining;
  opts.unusedPredicateDefinitionRemoval = unusedPredicateDefinitionRemoval;

  return preprocess(opts);
}

Problem Problem::inlinePredicateDefinitions(InliningMode mode)
{
  CALL("Problem::inlinePredicateDefinitions");

  if(mode==INL_OFF) {
    throw ApiException("Cannot perform definition inlining in function inlinePredicateDefinitions(InliningMode) with mode INL_OFF");
  }

  PreprocessingOptions opts;
  opts.mode = PM_EARLY_PREPROCESSING;
  opts.predicateDefinitionInlining = mode;
  opts.unusedPredicateDefinitionRemoval = false;

  return preprocess(opts);
}

Problem Problem::removeUnusedPredicateDefinitions()
{
  CALL("Problem::removeUnusedPredicateDefinitions");

  PreprocessingOptions opts;
  opts.mode = PM_EARLY_PREPROCESSING;
  opts.predicateDefinitionInlining = INL_OFF;
  opts.unusedPredicateDefinitionRemoval = true;

  return preprocess(opts);
}

Problem Problem::preprocessInStages(size_t stageCount, const PreprocessingOptions* stageSpecs)
{
  CALL("Problem::preprocessInStages");

  Problem res = *this;
  for(size_t idx=0; idx<stageCount; idx++) {
    res = res.preprocess(stageSpecs[idx]);
  }
  return res;
}

void Problem::readStageSpecs(vstring stagesStr, size_t& stageCnt, PreprocessingOptions*& stageSpecs)
{
  CALL("Problem::readStageSpecs");

  Stack<vstring> singleSpecs;
  StringUtils::splitStr(stagesStr.c_str(), ';', singleSpecs);

  stageCnt = singleSpecs.size();
  stageSpecs = new PreprocessingOptions[stageCnt];

  unsigned idx = 0;

  Stack<vstring>::BottomFirstIterator specIt(singleSpecs);
  while(specIt.hasNext()) {
    vstring spec = specIt.next();
    stageSpecs[idx] = PreprocessingOptions(spec);
    idx++;
  }
  ASS_EQ(idx,stageCnt);
}


Problem Problem::preprocessInStages(vstring stagesStr)
{
  CALL("Problem::preprocessInStages");

  size_t stageCnt;
  PreprocessingOptions* stageSpecs;

  readStageSpecs(stagesStr, stageCnt, stageSpecs);

  Problem res = preprocessInStages(stageCnt, stageSpecs);

  delete[] stageSpecs;
  return res;
}

Problem Problem::singlePreprocessingIteration(const PreprocessingOptions& options)
{
  CALL("Problem::singlePreprocessingIteration");

  Problem res = *this;

  if(options.sineSelection) {
    res = SineSelector(options.sineTolerance, options.sineDepthLimit).transform(res);
  }
  if(options.mode==PM_SELECTION_ONLY) {
    return res;
  }

  if(options.variableEqualityPropagation) {
    res = VariableEqualityPropagator().transform(res);
  }

  if(options.predicateIndexIntroduction) {
    res = PredicateIndexIntroducer().transform(res);
  }

  if(options.predicateDefinitionMerging) {
    res = PredicateDefinitionMerger().transform(res);
  }

  if(options.equivalenceDiscovery!=ED_NONE) {
    res = PredicateEquivalenceDiscoverer(options.equivalenceDiscovery,
	options.equivalenceDiscoverySatConflictLimit, options.equivalenceDiscoveryRandomSimulation,
	options.equivalenceDiscoveryAddImplications,
	options.equivalenceDiscoveryRetrievePremises,
	options._predicateEquivalenceDiscoveryRestricted,
	*options._ods.pedSet1,*options._ods.pedSet2).transform(res);
  }

  if(options.eprSkolemization) {
    res = EPRSkolemizer().transform(res);
  }

inlining:

  if(options.predicateDefinitionInlining!=INL_OFF) {
    if(options.predicateDefinitionInlining==INL_EPR_RESTORING) {
      res = EPRRestoringInliner().transform(res);
    }
    else {
      res = PredicateDefinitionInliner(options.predicateDefinitionInlining).transform(res);
    }
  }

  if(options.flatteningTopLevelConjunctions) {
    size_t sz0 = res.size();
    res = TopLevelFlattener().transform(res);
    if(res.size()!=sz0) {
      goto inlining;
    }
  }

  if(options.aigBddSweeping) {
    res = BDDSweeper(options.aigBddSweepingMaximumBddAtomCount).transform(res);
  }

  if(options.aigInlining) {
    res = AIGInliner().transform(res);
  }

  if(options.aigConditionalRewriting) {
    res = AIGConditionalRewriter().transform(res);
  }

  if(options.aigDefinitionIntroduction) {
    res = AIGDefinitionIntroducer().transform(res);
  }

  if(options.unusedPredicateDefinitionRemoval) {
    res = UnusedPredicateDefinitionRemover().transform(res);
  }

  unsigned arCnt = options._ods.lhs->size();
  if(arCnt>0) {
    res = res.performAsymetricRewriting(arCnt, options._ods.lhs->begin(), options._ods.posRhs->begin(),
	options._ods.negRhs->begin(), options._ods.dblRhs->begin());
  }

  if(options.mode==PM_EARLY_PREPROCESSING) {
    return res;
  }

  bool oldTraceVal = env.options->showNonconstantSkolemFunctionTrace();
  env.options->setShowNonconstantSkolemFunctionTrace(options.showNonConstantSkolemFunctionTrace);

  res = Clausifier(options.namingThreshold, options.preserveEpr, options.mode==PM_SKOLEMIZE).transform(res);

  env.options->setShowNonconstantSkolemFunctionTrace(oldTraceVal);
  return res;
}

Problem Problem::preprocess(const PreprocessingOptions& options)
{
  CALL("Problem::preprocess");
  options.validate();

  Problem res = *this;

  res = Preprocessor1().transform(res);

  unsigned iterIdx = 0;
  for(;;) {
    if(options.repetitionCount && iterIdx>=options.repetitionCount) {
      break;
    }

    Problem old = res;

    res = res.singlePreprocessingIteration(options);

    if(fixpointReached(options.repetitionEarlyTermination, old, res)) {
      break;
    }

    iterIdx++;
  }

  return res;
}

bool Problem::fixpointReached(FixpointCheck fc, Problem& oldPrb, Problem& newPrb)
{
  CALL("Problem::fixpointReached");

  switch(fc) {
  case FC_NONE:
    return false;
  case FC_FORMULA_COUNT:
    return oldPrb.size()==newPrb.size();
  default:
    ASSERTION_VIOLATION;
  }
}

Problem Problem::performAsymetricRewriting(Formula lhs, Formula posRhs, Formula negRhs, Formula dblRhs)
{
  CALL("Problem::performAsymetricRewriting");

  return performAsymetricRewriting(1, &lhs, &posRhs, &negRhs, &dblRhs);
}

Problem Problem::performAsymetricRewriting(size_t cnt, Formula* lhsArray, Formula* posRhsArray, Formula* negRhsArray,
    Formula* dblRhsArray)
{
  CALL("Problem::performAsymetricRewriting");

  Problem res = Preprocessor1().transform(*this);
  PredicateDefinitionInliner inl(INL_NO_DISCOVERED_DEFS);
  for(size_t i=0; i<cnt; i++) {
    if(!inl.addAsymetricDefinition(lhsArray[i], posRhsArray[i], negRhsArray[i], dblRhsArray[i])) {
      throw new ApiException("LHS is already defined");
    }
  }
  res = inl.transform(res);
  return res;
}

void outputAttributes(ostream& out, FBHelperCore::AttribStack* attribs)
{
  CALL("outputAttributes");

  if(!attribs) {
    return;
  }
  FBHelperCore::AttribStack::BottomFirstIterator it(*attribs);
  while(it.hasNext()) {
    FBHelperCore::AttribPair attr = it.next();
    out << " | $attr(" << attr.first << ", " << attr.second <<")";
  }
}

void outputSymbolTypeDefinitions(ostream& out, unsigned symNumber, bool function, bool outputAllTypeDefs,
    FBHelperCore::AttribStack* attribs, bool dummyNames)
{
  CALL("outputSymbolTypeDefinitions");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);

  if(sym->interpreted()) {
    //there is no need to output type definitions for interpreted symbols
    return;
  }

  BaseType* type = function ? static_cast<BaseType*>(sym->fnType()) : sym->predType();

  if(!outputAllTypeDefs && type->isAllDefault()) {
    return;
  }

  vstring symName = dummyNames ? (DefaultHelperCore::getDummyName(!function, symNumber)) : sym->name();

  out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ",type, "
      << symName << ": ";

  unsigned arity = sym->arity();
  if(arity>0) {
    if(arity==1) {
      out << env.sorts->sortName(type->arg(0));
    }
    else {
      out << "(";
      for(unsigned i=0; i<arity; i++) {
	if(i>0) {
	  out << " * ";
	}
	out << env.sorts->sortName(type->arg(i));
      }
      out << ")";
    }
    out << " > ";
  }
  if(function) {
    out << env.sorts->sortName(sym->fnType()->result());
  }
  else {
    out << "$o";
  }
  outputAttributes(out, attribs);
  out << " )." << endl;

}

void Problem::outputTypeDefinitions(ostream& out, bool outputAllTypeDefs)
{
  CALL("Problem::outputTypeDefinitions");

  DefaultHelperCore* core0 = _data->getCore();
  bool dummyNames = core0 && core0->outputDummyNames();
  FBHelperCore* core = (core0 && core0->isFBHelper()) ? static_cast<FBHelperCore*>(core0) : 0;
  unsigned sorts = env.sorts->count();
  for(unsigned i=Sorts::FIRST_USER_SORT; i<sorts; i++) {
    out << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i) << ": $tType";
    if(core) { outputAttributes(out, &core->getSortAttributes(i)); }
    out << " )." << endl;
  }


  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(out, i, true, outputAllTypeDefs,
	core ? &core->getFunctionAttributes(i) : 0, dummyNames);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(out, i, false, outputAllTypeDefs,
	core ? &core->getPredicateAttributes(i) : 0, dummyNames);
  }
}

void Problem::output(ostream& out, bool outputTypeDefs, bool outputAllTypeDefs)
{
  CALL("Problem::output");

  if(outputTypeDefs) {
    outputTypeDefinitions(out, outputAllTypeDefs);
  }
  AnnotatedFormulaIterator afit = formulas();
  while(afit.hasNext()) {
    out<<afit.next()<<endl;
  }
}

void Problem::outputStatistics(ostream& out)
{
  CALL("Problem::outputStatictics");

  env.statistics->print(out);
}

///////////////////////////////////////
// Iterating through the problem

bool AnnotatedFormulaIterator::hasNext()
{
  CALL("AnnotatedFormulaIterator::hasNext");

  AFList** plst=static_cast<AFList**>(idata);

  if(ready) {
    return *plst;
  }
  //we need to advance to the next element of the list
  ASS(*plst); //we're not at the end of the list
  plst=(*plst)->tailPtr();
  idata=plst;
  ready=true;
  return *plst;
}

AnnotatedFormula AnnotatedFormulaIterator::next()
{
  CALL("AnnotatedFormulaIterator::next");

  AFList** plst=static_cast<AFList**>(idata);
  ASS(ready);
  ASS(*plst); //we're not at the end of the list
  ready=false;
  return (*plst)->head();
}

void AnnotatedFormulaIterator::del()
{
  CALL("AnnotatedFormulaIterator::del");

  AFList** plst=static_cast<AFList**>(idata);
  ASS(*plst); //we're not at the end of the list

  AFList* removedLink=*plst;
  *plst=removedLink->tail();
  delete removedLink;
}


AnnotatedFormulaIterator Problem::formulas()
{
  CALL("Problem::formulas");

  AnnotatedFormulaIterator res;
  res.idata=&_data->forms();
  res.ready=true;
  return res;
}

} // namespace Api
