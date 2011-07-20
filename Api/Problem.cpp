/**
 * @file Problem.cpp
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
#include "Lib/ScopedLet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/CNF.hpp"
#include "Shell/EPRInlining.hpp"
#include "Shell/EPRSkolem.hpp"
#include "Shell/EqualityPropagator.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/FormulaIteExpander.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/LispParser.hpp"
#include "Shell/Naming.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/PDInliner.hpp"
#include "Shell/PDMerger.hpp"
#include "Shell/PredicateDefinition.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/SimplifyProver.hpp"
#include "Shell/SineUtils.hpp"
#include "Shell/SpecialTermElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/VarManager.hpp"


namespace Api
{

using namespace Lib;

Problem::PreprocessingOptions::OptDataStore::OptDataStore()
{
  CALL("Problem::PreprocessingOptions::ARRStore::ARRStore()");

  lhs = new Stack<Formula>();
  posRhs = new Stack<Formula>();
  negRhs = new Stack<Formula>();
  dblRhs = new Stack<Formula>();
  builtInPreds = new Stack<unsigned>();
}

Problem::PreprocessingOptions::OptDataStore::OptDataStore(const OptDataStore& o)
{
  CALL("Problem::PreprocessingOptions::ARRStore::ARRStore(const ARRStore&)");

  lhs = new Stack<Formula>(*o.lhs);
  posRhs = new Stack<Formula>(*o.posRhs);
  negRhs = new Stack<Formula>(*o.negRhs);
  dblRhs = new Stack<Formula>(*o.dblRhs);
  builtInPreds = new Stack<unsigned>(*o.builtInPreds);
}

Problem::PreprocessingOptions::OptDataStore& Problem::PreprocessingOptions::OptDataStore::operator=(const OptDataStore& o)
{
  CALL("Problem::PreprocessingOptions::ARRStore::operator=");

  *lhs = *o.lhs;
  *posRhs = *o.posRhs;
  *negRhs = *o.negRhs;
  *dblRhs = *o.dblRhs;
  *builtInPreds = *o.builtInPreds;
  return *this;
}

Problem::PreprocessingOptions::OptDataStore::~OptDataStore()
{
  CALL("Problem::PreprocessingOptions::ARRStore::~ARRStore");

  delete lhs;
  delete posRhs;
  delete negRhs;
  delete dblRhs;
  delete builtInPreds;
}


Problem::PreprocessingOptions::PreprocessingOptions(
    PreprocessingMode mode,
    int namingThreshold, bool preserveEpr, InliningMode predicateDefinitionInlining,
    bool unusedPredicateDefinitionRemoval, bool showNonConstantSkolemFunctionTrace,
    bool traceInlining, bool sineSelection, float sineTolerance, unsigned sineDepthLimit,
    bool variableEqualityPropagation, bool traceVariableEqualityPropagation,
    bool eprSkolemization, bool traceEPRSkolemization,
    bool predicateDefinitionMerging, bool tracePredicateDefinitionMerging)
: mode(mode), namingThreshold(namingThreshold), preserveEpr(preserveEpr),
  predicateDefinitionInlining(predicateDefinitionInlining),
  unusedPredicateDefinitionRemoval(unusedPredicateDefinitionRemoval),
  showNonConstantSkolemFunctionTrace(showNonConstantSkolemFunctionTrace),
  traceInlining(traceInlining), sineSelection(sineSelection),
  sineTolerance(sineTolerance), sineDepthLimit(sineDepthLimit),
  variableEqualityPropagation(variableEqualityPropagation),
  traceVariableEqualityPropagation(traceVariableEqualityPropagation),
  eprSkolemization(eprSkolemization),
  traceEPRSkolemization(traceEPRSkolemization),
  predicateDefinitionMerging(predicateDefinitionMerging),
  tracePredicateDefinitionMerging(tracePredicateDefinitionMerging)
{
  CALL("Problem::PreprocessingOptions::PreprocessingOptions");
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

void Problem::PreprocessingOptions::addBuiltInPredicate(Predicate pred)
{
  CALL("Problem::PreprocessingOptions::addBuiltInPredicate");

  _ods.builtInPreds->push(pred);
}

void Problem::PreprocessingOptions::validate() const
{
  CALL("Problem::PreprocessingOptions::validate");

  if(namingThreshold>32767 || namingThreshold<0) {
    throw new ApiException("namingThreshold must be in the range [0,32767]");
  }

  if(sineSelection && sineTolerance<1.0f) {
    throw new ApiException("sineTolerance must be greater than or equal to 1");
  }
}

typedef List<AnnotatedFormula> AFList;

class Problem::PData
{
public:
  PData() : _size(0), _forms(0), _refCnt(0)
  {
  }
  ~PData()
  {
    _forms->destroy();
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

    obj->_forms=_forms->copy();
  }

  void addFormula(AnnotatedFormula f)
  {
    CALL("Problem::PData::addFormula");

    _size++;
    AFList::push(f, _forms);
  }

  size_t size() { return _size; }

  AFList*& forms() { return _forms; }

  DefaultHelperCore* getCore() {
    CALL("Problem::PData::getCore");
    if(!_forms) { return 0; }
    return *_forms->head()._aux;
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
  CALL("Problem::addFormula");

  return _data->size();
}



///////////////////////////////////////
// Parsing

void Problem::addFromStream(istream& s, string includeDirectory, bool simplifySyntax)
{
  CALL("Problem::addFromStream");

  using namespace Shell;

  string originalInclude=env.options->include();
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
    TPTPLexer lexer(s);
    TPTPParser parser(lexer);
    units = parser.units();
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
    _origName = f.name();
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

    string unitName;
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
  string _origName;
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
    fu = SpecialTermElimination().apply(fu, newDefs);
    handleDefs(newDefs);

    fu = Rectify::rectify(fu);
    fu = SimplifyFalseTrue::simplify(fu);
    fu = Flattening::flatten(fu);

    fu = FormulaIteExpander().apply(fu, newDefs);
    handleDefs(newDefs);

    addUnit(fu);
  }
};

class Problem::VariableEqualityPropagator : public ProblemTransformer
{
public:
  VariableEqualityPropagator(bool trace) : _eqProp(trace) {}
protected:
  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::VariableEqualityPropagator::transformImpl");

    addUnit(_eqProp.apply(unit));
  }
  EqualityPropagator _eqProp;
};

class Problem::PredicateDefinitionMerger : public ProblemTransformer
{
public:
  PredicateDefinitionMerger(bool trace)
      : _trace(trace), _merger(trace)
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
    units->destroy();

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      transform(f);
    }
  }

  void transformImpl(Kernel::Unit* unit)
  {
    CALL("Problem::PredicateDefinitionMerger::transformImpl");

    Kernel::Unit* res = _merger.apply(unit);
    if(res) {
      addUnit(res);
    }
  }

  bool _trace;
  Shell::PDMerger _merger;
};

class Problem::PredicateDefinitionInliner : public ProblemTransformer
{
public:
  PredicateDefinitionInliner(InliningMode mode, bool trace)
      : _mode(mode), _pdInliner(mode==INL_AXIOMS_ONLY, trace)
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

    AnnotatedFormulaIterator fit;
    if(_mode!=INL_NO_DISCOVERED_DEFS) {
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
  EPRRestoringInliner(bool trace)
      : _trace(trace), _eprInliner(trace)
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl(Problem)");

    p = PredicateDefinitionInliner(INL_PREDICATE_EQUIVALENCES_ONLY, _trace).transform(p);

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _eprInliner.scan(units);
    units->destroy();

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

  bool _trace;
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
  EPRSkolemizer(bool trace)
      : _trace(trace), _eprSkolem(trace)
  {
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::EPRRestoringInliner::transformImpl(Problem)");

    p = ConstantSkolemizer().transform(p);
    p = PredicateDefinitionInliner(INL_PREDICATE_EQUIVALENCES_ONLY, _trace).transform(p);

    Kernel::UnitList* units = 0;

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      Kernel::UnitList::push(f.unit, units);
    }
    _eprSkolem.scan(units);
    units->destroy();

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

  bool _trace;
  Shell::EPRSkolem _eprSkolem;
};


class Problem::UnusedPredicateDefinitionRemover : public ProblemTransformer
{
public:
  UnusedPredicateDefinitionRemover(Stack<unsigned>* builtInPreds=0)
  {
    CALL("Problem::UnusedPredicateDefinitionRemover");
    if(builtInPreds) {
      Stack<unsigned>::Iterator bipIt(*builtInPreds);
      while(bipIt.hasNext()) {
	unsigned pred = bipIt.next();
	pd.addBuiltInPredicate(pred);
      }
    }
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
    units->destroy();

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

Problem Problem::preprocess(const PreprocessingOptions& options)
{
  CALL("Problem::preprocess");
  options.validate();

  Problem res = *this;

  res = Preprocessor1().transform(res);

  if(options.sineSelection) {
    res = SineSelector(options.sineTolerance, options.sineDepthLimit).transform(res);
  }
  if(options.mode==PM_SELECTION_ONLY) {
    return res;
  }

  if(options.variableEqualityPropagation) {
    res = VariableEqualityPropagator(options.traceVariableEqualityPropagation).transform(res);
  }

  if(options.predicateDefinitionMerging) {
    res = PredicateDefinitionMerger(options.tracePredicateDefinitionMerging).transform(res);
  }

  if(options.eprSkolemization) {
    res = EPRSkolemizer(options.traceEPRSkolemization).transform(res);
  }

  if(options.predicateDefinitionInlining!=INL_OFF) {
    if(options.predicateDefinitionInlining==INL_EPR_RESTORING) {
      res = EPRRestoringInliner(options.traceInlining).transform(res);
    }
    else {
      res = PredicateDefinitionInliner(options.predicateDefinitionInlining,options.traceInlining).transform(res);
    }
  }

  if(options.unusedPredicateDefinitionRemoval) {
    res = UnusedPredicateDefinitionRemover(options._ods.builtInPreds).transform(res);
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
  PredicateDefinitionInliner inl(INL_NO_DISCOVERED_DEFS, false);
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
    FBHelperCore::AttribStack* attribs)
{
  CALL("outputSymbolTypeDefinitions");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);
  BaseType* type = function ? static_cast<BaseType*>(sym->fnType()) : sym->predType();

  if(!outputAllTypeDefs && type->isAllDefault()) {
    return;
  }

  out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ",type, "
      << sym->name() << ": ";

  unsigned arity = sym->arity();
  if(arity>0) {
    out << "(";
    for(unsigned i=0; i<arity; i++) {
      if(i>0) {
	out << " * ";
      }
      out << env.sorts->sortName(type->arg(i));
    }
    out << ") > ";
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
  FBHelperCore* core = (core0 && core0->isFBHelper()) ? static_cast<FBHelperCore*>(core0) : 0;
  unsigned sorts = env.sorts->sorts();
  for(unsigned i=Sorts::FIRST_USER_SORT; i<sorts; i++) {
    out << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i) << ": $tType";
    if(core) { outputAttributes(out, &core->getSortAttributes(i)); }
    out << " )." << endl;
  }


  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(out, i, true, outputAllTypeDefs,
	core ? &core->getFunctionAttributes(i) : 0);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(out, i, false, outputAllTypeDefs,
	core ? &core->getPredicateAttributes(i) : 0);
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


}
