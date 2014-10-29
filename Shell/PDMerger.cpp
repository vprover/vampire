/**
 * @file PDMerger.cpp
 * Implements class PDMerger.
 */

#include "Lib/Comparison.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/Sort.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaTransformer.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Shell/Options.hpp"

#include "PDUtils.hpp"
#include "Statistics.hpp"

#include "PDMerger.hpp"

namespace Shell
{

Comparison PDMerger::UnitComparator::compare(Unit* u1, Unit* u2)
{
  return Int::compare(u1->number(), u2->number());
}

/////////////////////////
// PDMerger::Normalizer
//

class PDMerger::Normalizer : public FormulaTransformer
{
public:
  static Comparison compare(Formula* f1, Formula* f2);
  static Comparison compare(Literal* lit1, Literal* lit2);

protected:
  Formula* applyJunction(Formula* f);

private:

};

Formula* PDMerger::Normalizer::applyJunction(Formula* f)
{
  CALL("PDMerger::Normalizer::applyJunction");

  Stack<Formula*> res;
  res.reset();

  bool modified = false;

  FormulaList* args = f->args();
  FormulaList::Iterator it(args);
  while(it.hasNext()) {
    Formula* arg = it.next();
    Formula* newArg = apply(arg);
    if(newArg!=arg) {
      modified = true;
    }
    res.push(newArg);
  }
  Lib::sort<Normalizer>(res.begin(), res.end());

  if(!modified && iteratorsEqual(FormulaList::Iterator(args),
				 Stack<Formula*>::BottomFirstIterator(res))) {
    return f;
  }
  FormulaList* newArgs = 0;
  FormulaList::pushFromIterator(Stack<Formula*>::TopFirstIterator(res), newArgs);
  ASS_EQ(args->length(), newArgs->length());
  return new JunctionFormula(f->connective(), newArgs);
}

Comparison PDMerger::Normalizer::compare(Formula* fm1, Formula* fm2)
{
  CALL("PDMerger::Normalizer::compare(Formula*...)");

  SubformulaIterator sf1(fm1);
  SubformulaIterator sf2(fm2);

  while (sf1.hasNext()) {
    if (! sf2.hasNext()) {
      return GREATER;
    }
    Formula* f1 = sf1.next();
    Formula* f2 = sf2.next();

    Comparison comp = Int::compare((int)f1->connective(), (int)f2->connective());
    if (comp != EQUAL) {
      return comp;
    }

    // same connective
    switch (f1->connective()) {
    case LITERAL:
      comp = compare(f1->literal(),f2->literal());
      if (comp != EQUAL) {
	return comp;
      }
      break;

    case FORALL:
    case EXISTS:
      comp = Int::compare(f1->vars()->length(),f2->vars()->length());
      if (comp != EQUAL) {
	return comp;
      }
      break;

    default:
      break;
    }
  }
  return sf2.hasNext() ? LESS : EQUAL;
}

Comparison PDMerger::Normalizer::compare(Literal* l1, Literal* l2)
{
  CALL("PDMerger::Normalizer::compare(Literal*...)");

  if (l1 == l2) {
    return EQUAL;
  }

  Comparison comp = Int::compare(l1->weight(), l2->weight());
  if (comp != EQUAL) {
    return comp;
  }

  comp = Int::compare(l1->header(), l2->header());
  if (comp != EQUAL) {
    return comp;
  }

  comp = Int::compare(l1->vars(),l2->vars());
  if (comp != EQUAL) {
    return comp;
  }

  comp = Int::compare(l1->getDistinctVars(), l2->getDistinctVars());
  if (comp != EQUAL) {
    return comp;
  }

  SubtermIterator stIt1(l1);
  SubtermIterator stIt2(l2);
  while(stIt1.hasNext()) {
    if(!stIt2.hasNext()) {
      return GREATER;
    }
    TermList t1 = stIt1.next();
    TermList t2 = stIt2.next();

    if(t1.isVar()) {
      if(t2.isVar()) {
	continue;
      }
      return GREATER;
    }
    if(t2.isVar()) {
      return LESS;
    }
    comp = Int::compare(t1.term()->functor(),t2.term()->functor());
    if (comp != EQUAL) {
      return comp;
    }
  }

  return stIt2.hasNext() ? LESS : EQUAL;
}


///////////////////////
// PDMerger
//

PDMerger::PDMerger(bool trace)
: //  _index(new StringFormulaIndex())
  _index(new AIGFormulaIndex())
{
  CALL("PDMerger::PDMerger");

  _pred2Defs.init(env -> signature->predicates(), 0);
}

PDMerger::~PDMerger()
{
  CALL("PDMerger::~PDMerger");

  unsigned preds = env -> signature->predicates();
  for(unsigned i=0; i<preds; i++) {
    if(_pred2Defs[i]) {
      delete _pred2Defs[i];
    }
  }
}

void PDMerger::handleIndexes(FormulaUnit* unit, bool insert)
{
  CALL("PDMerger::removeFromIndexes");

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(unit, lhs, rhs);

  if(insert) {
    _index->insert(unit, rhs);
  }
  else {
    _index->remove(unit, rhs);
  }

  static Stack<unsigned> preds;
  preds.reset();
  rhs->collectPredicates(preds);

  makeUnique(preds);
  Stack<unsigned>::Iterator pit(preds);
  while(pit.hasNext()) {
    unsigned pred = pit.next();
    if(!_pred2Defs[pred]) {
      continue;
    }
    if(insert) {
      _pred2Defs[pred]->insert(unit);
    }
    else {
      _pred2Defs[pred]->remove(unit);
    }
  }
}

/**
 * Add definitions affected by eliminating predicate @c elPred.
 */
void PDMerger::triggerNewDefinitions(unsigned elPred)
{
  CALL("PDMerger::triggerNewDefinitions");
  ASS_REP(_pred2Defs[elPred], env -> signature->predicateName(elPred));

  FormulaSkipList* sl = _pred2Defs[elPred];
  _pred2Defs[elPred] = 0;

  while(sl->isNonEmpty()) {
    FormulaUnit* u = sl->pop();
    handleIndexes(u, false);
    _unprocessed.push_back(u);
  }
  delete sl;
}

void PDMerger::processDefinition(FormulaUnit* unit0)
{
  CALL("PDMerger::processDefinition");

  FormulaUnit* unit = unit0;

  unit = _inliner.apply(unit);

  if(!PDUtils::hasDefinitionShape(unit)) {
    return;
  }

  Normalizer norm;
  FTFormulaUnitTransformer<Normalizer> unitNorm(Inference::NORMALIZATION, norm);
  unit = unitNorm.transform(unit);

  Literal* lhs;
  Formula* rhs;
  PDUtils::splitDefinition(unit, lhs, rhs);

  FormulaQueryResultIterator resIt = _index->getEquivalent(rhs);
  while(resIt.hasNext()) {
    FormulaQueryResult qres = resIt.next();

    Literal* qrLhs;
    Formula* qrRhs;
    PDUtils::splitDefinition(qres.unit, qrLhs, qrRhs);

    if(qrLhs->arity()!=lhs->arity()) {
      continue;
    }

    Literal* substLhs = qres.substitution->applyToQuery(lhs);
    Literal* substQrLhs = qres.substitution->applyToResult(qrLhs);

    if(substQrLhs->functor()==substLhs->functor()) {
      continue;
    }

    if(!substLhs->containsAllVariablesOf(substQrLhs)) {
      continue;
    }
    ASS(substQrLhs->containsAllVariablesOf(substLhs))

    Formula* resRhs = new AtomicFormula(substQrLhs);

    Formula* merged = new BinaryFormula(IFF, new AtomicFormula(substLhs), resRhs);
    Formula::VarList* freeVars = merged->freeVariables();
    if(freeVars) {
      merged = new QuantifiedFormula(FORALL, freeVars, merged);
    }

    Inference* inf = new Inference2(Inference::PREDICATE_DEFINITION_MERGING, unit, qres.unit);
    Unit::InputType inpType = Unit::getInputType(unit->inputType(), qres.unit->inputType());
    FormulaUnit* premise = new FormulaUnit(merged, inf, inpType);

    env -> statistics->mergedPredicateDefinitions++;

    if (env->options->showPreprocessing()) {
      env->beginOutput();
      env->out() << "[PP] Predicate equivalence discovered\n- " << qres.unit->toString()
                << "\n- " << unit->toString() << "\n- resulting into " 
                << premise->toString() << std::endl;
      env->endOutput();
    }    

#if 0
    if(!_inliner.tryGetDef(premise, substLhs, resRhs)) {      
      ASSERTION_VIOLATION;
    }
#else
    ALWAYS(_inliner.tryGetDef(premise, substLhs, resRhs));
#endif

    ALWAYS(_replacements.insert(unit0, 0));
    triggerNewDefinitions(substLhs->functor());
    return;
  }
  handleIndexes(unit, true);
  if(unit!=unit0) {
    ALWAYS(_replacements.insert(unit0, unit));
  }
}

FormulaUnit* PDMerger::apply(FormulaUnit* unit)
{
  CALL("PDMerger::apply(FormulaUnit*)");

  if(!PDUtils::hasDefinitionShape(unit)) {
    return _inliner.apply(unit);
  }

  while(unit && _replacements.find(unit, unit)) {}
  if(unit) {
    unit = _inliner.apply(unit);
  }
  return unit;
}

Unit* PDMerger::apply(Unit* unit)
{
  CALL("PDMerger::apply(Unit*)");

  if(unit->isClause()) {
    return _inliner.apply(unit);
  }
  return apply(static_cast<FormulaUnit*>(unit));
}

void PDMerger::scan(UnitList* units)
{
  CALL("PDMerger::scan");

  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    if(!PDUtils::hasDefinitionShape(fu)) {
      continue;
    }
    if(_inliner.tryGetPredicateEquivalence(fu)) {
      _replacements.insert(fu, 0);

      unsigned pred1, pred2;
      ALWAYS(PDUtils::isPredicateEquivalence(fu, pred1, pred2));
      if(!_pred2Defs[pred1]) {
	_pred2Defs[pred1] = new FormulaSkipList();
      }
      if(!_pred2Defs[pred2]) {
	_pred2Defs[pred2] = new FormulaSkipList();
      }
    }
    else {
      _unprocessed.push_back(fu);

      Literal* lhs;
      Formula* rhs;
      PDUtils::splitDefinition(fu, lhs, rhs);
      unsigned pred = lhs->functor();
      if(!_pred2Defs[pred]) {
	_pred2Defs[pred] = new FormulaSkipList();
      }
    }
  }

  while(_unprocessed.isNonEmpty()) {
    FormulaUnit* fu = _unprocessed.pop_front();
    processDefinition(fu);
  }
}

void PDMerger::apply(Problem& prb)
{
  CALL("PDMerger::apply(Problem&)");

  if(apply(prb.units())) {
    prb.invalidateProperty();
  }
}

bool PDMerger::apply(UnitList*& units)
{
  CALL("PDMerger::apply(UnitList*&)");

  scan(units);

  bool modified = false;
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newUnit = apply(u);
    if(u==newUnit) {
      continue;
    }
    modified = true;
    if(newUnit) {
      uit.replace(newUnit);
    }
    else {
      uit.del();
    }
  }

  if (env->options->showPreprocessing()) {
    env->beginOutput();
    ostream& out = env->out();
    
    unsigned defCnt = 0;
    UnitList::Iterator uit2(units);
    while(uit2.hasNext()) {
      Unit* u = uit2.next();
      if(u->isClause()) {
        continue;
      }
      if(PDUtils::hasDefinitionShape(static_cast<FormulaUnit*>(u))) {
//        out << "Survivor: " << u->toString() << endl;
        defCnt++;
      }
    }
    out << "Merged " << env->statistics->mergedPredicateDefinitions << ", "
        << defCnt << " survived" << endl;
        
    env->endOutput();
  }
  
  return modified;
}


}
