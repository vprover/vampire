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
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/CNF.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/FormulaIteExpander.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/LispParser.hpp"
#include "Shell/Naming.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/PDInliner.hpp"
#include "Shell/PredicateDefinition.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/SimplifyFalseTrue.hpp"
#include "Shell/SimplifyProver.hpp"
#include "Shell/SpecialTermElimination.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/VarManager.hpp"


namespace Api
{

using namespace Lib;

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
  virtual Problem transform(Problem p)
  {
    CALL("ProblemTransformer::transform(Problem)");

    Problem res;
    _res = &res;

    transformImpl(p);

    _res = 0;
    return res;
  }

protected:
  ProblemTransformer() :
    _transforming(false), _nextDefNum(1), _res(0) {}

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
    _nextResNum = 1;
    _origName = f.name();
    _origUnit = f;
    _origAF = f;
    ASS(!VarManager::varNamePreserving());
    VarManager::setVarNamePreserving(f._aux->getVarFactory());

    _transformingDef = false;
    transformImpl(f);

    _transformingDef = true;
    while(_defs.isNonEmpty()) {
      transformImpl(_defs.pop_front());
    }

    _transforming = false;
    VarManager::setVarNamePreserving(0);
  }

  void addUnit(Kernel::Unit* unit)
  {
    CALL("Problem::ProblemTransformer::addUnit");

    AnnotatedFormula af = AnnotatedFormula(unit, _origAF._aux);
    _res->addFormula(af);

    if(unit==_origUnit) {
      //if added formula is the original one, we don't proceed
      //creating a new name for it
      return;
    }
    string unitName;
    if(_transformingDef) {
      unitName="def_"+Int::toString(_nextDefNum);
      _nextDefNum++;
    }
    else {
      unitName=_origName+"_"+Int::toString(_nextResNum);
      _nextResNum++;
    }
    Parser::assignAxiomName(unit, unitName);
  }

  void handleDefs(Kernel::UnitList*& defLst)
  {
    CALL("Problem::ProblemTransformer::addUnit");

    while(defLst) {
      _defs.push_back(Kernel::UnitList::pop(defLst));
    }
  }

  bool _transforming;
  bool _transformingDef;
  unsigned _nextResNum;
  string _origName;
  Kernel::Unit* _origUnit;
  AnnotatedFormula _origAF;

  Deque<Kernel::Unit*> _defs;

  unsigned _nextDefNum;
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

    Kernel::UnitList* newDefs=0;
    unit = SpecialTermElimination().apply(static_cast<Kernel::FormulaUnit*>(unit), newDefs);
    handleDefs(newDefs);

    unit = Rectify::rectify(unit);
    unit = SimplifyFalseTrue::simplify(unit);
    unit = Flattening::flatten(unit);

    {
      unit = FormulaIteExpander().apply(unit, newDefs);
      handleDefs(newDefs);
    }

    addUnit(unit);
  }
};

class Problem::PredicateDefinitionInliner : public ProblemTransformer
{
public:
  PredicateDefinitionInliner(InliningMode mode)
      : pdInliner(mode==INL_AXIOMS_ONLY)
  {
    ASS_NEQ(mode, INL_OFF);
  }

protected:
  virtual void transformImpl(Problem p)
  {
    CALL("Problem::PredicateDefinitionInliner::transformImpl(Problem)");

    static DHSet<Kernel::Unit*> defs;
    defs.reset();

    AnnotatedFormulaIterator fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      if(f.unit->isClause()) {
	continue;
      }
      FormulaUnit* fu = static_cast<FormulaUnit*>(f.unit);
      if(pdInliner.tryGetPredicateEquivalence(fu)) {
	defs.insert(fu);
      }
    }

    fit=p.formulas();
    while(fit.hasNext()) {
      AnnotatedFormula f=fit.next();
      if(f.unit->isClause() || defs.contains(f.unit)) {
	continue;
      }
      FormulaUnit* fu = static_cast<FormulaUnit*>(f.unit);
      if(pdInliner.tryGetDef(fu)) {
	defs.insert(fu);
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

    addUnit(pdInliner.apply(unit));
  }

  Shell::PDInliner pdInliner;
};

class Problem::UnusedPredicateDefinitionRemover : public ProblemTransformer
{
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

    unit = NNF::ennf(unit);
    unit = Flattening::flatten(unit);

    if(!_transformingDef && namingThreshold) {
      Kernel::UnitList* newDefs=0;
      unit = naming.apply(unit,newDefs);
      handleDefs(newDefs);
    }

    unit = NNF::nnf(unit);
    unit = Flattening::flatten(unit);
    unit = Skolem::skolemise(unit);
    if(onlySkolemize) {
      addUnit(unit);
    }
    else {
      if(!_transformingDef && namingThreshold && preserveEpr) {
	Kernel::UnitList* newDefs=0;
	unit = naming.apply(unit,newDefs);
	handleDefs(newDefs);
      }

      cnf.clausify(unit,auxClauseStack);
      while (! auxClauseStack.isEmpty()) {
	Unit* u = auxClauseStack.pop();
	addUnit(u);
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

  if(namingThreshold>32767 || namingThreshold<0) {
    throw new ApiException("namingThreshold must be in the range [0,32767]");
  }

  Problem res = Preprocessor1().transform(*this);
  if(predicateDefinitionInlining!=INL_OFF) {
    res = PredicateDefinitionInliner(predicateDefinitionInlining).transform(res);
  }
  if(unusedPredicateDefinitionRemoval) {
    res = UnusedPredicateDefinitionRemover().transform(res);
  }
  res = Clausifier(namingThreshold, preserveEpr, false).transform(res);
  return res;
}

Problem Problem::skolemize(int namingThreshold, bool preserveEpr, InliningMode predicateDefinitionInlining,
    bool unusedPredicateDefinitionRemoval)
{
  CALL("Problem::skolemize");

  if(namingThreshold>32767 || namingThreshold<0) {
    throw new ApiException("namingThreshold must be in the range [0,32767]");
  }

  Problem res = Preprocessor1().transform(*this);
  if(predicateDefinitionInlining!=INL_OFF) {
    res = PredicateDefinitionInliner(predicateDefinitionInlining).transform(res);
  }
  if(unusedPredicateDefinitionRemoval) {
    res = UnusedPredicateDefinitionRemover().transform(res);
  }
  res = Clausifier(namingThreshold, preserveEpr, true).transform(res);
  return res;
}

Problem Problem::inlinePredicateDefinitions(InliningMode mode)
{
  CALL("Problem::inlinePredicateDefinitions");

  if(mode==INL_OFF) {
    throw ApiException("Cannot perform definition inlining in function inlinePredicateDefinitions(InliningMode) with mode INL_OFF");
  }

  Problem res = Preprocessor1().transform(*this);
  res = PredicateDefinitionInliner(mode).transform(res);
  return res;
}

Problem Problem::removeUnusedPredicateDefinitions()
{
  CALL("Problem::removeUnusedPredicateDefinitions");

  Problem res = Preprocessor1().transform(*this);
  res = UnusedPredicateDefinitionRemover().transform(res);
  return res;
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
