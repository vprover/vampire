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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/BinaryResolution.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 

namespace {

void addToMapFromIterator(DHMap<Term*, TermQueryResult>& map, TermQueryResultIterator it) {
  while (it.hasNext()) {
    TermQueryResult tqr = it.next();
    ASS(tqr.term.isTerm());
    map.insert(tqr.term.term(), tqr);
  }
}

InferenceRule getGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getNonGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getInfRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getFinRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getDBRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

};  // namespace

TermList TermReplacement::transformSubterm(TermList trm)
{
  CALL("TermReplacement::transformSubterm");

  if(trm.isTerm() && trm.term()==_o){
    return _r;
  }
  return trm;
}

TermList SkolemSquashingTermReplacement::transformSubterm(TermList trm)
{
  CALL("SkolemSquashingTermReplacement::transformSubterm");

  if(trm.isTerm()) {
    auto t = trm.term();
    if (t==_o){
      return _r;
    }
    unsigned f = t->functor();
    if (env.signature->getFunction(f)->skolem()) {
      unsigned v;
      if (!_tv.find(t,v)) {
        v = _v++;
        _tv.insert(t,v);
      }
      return TermList(v,false);
    }
  }
  return trm;
}

Literal* replaceTermInLiteral(Literal* lit, Term* o, TermList r) {
  TermReplacement tr(o,r);
  return tr.transform(lit);
}

Literal* replaceTermAndSquashSkolemsInLiteral(Literal* lit, Term* o, TermList r, unsigned& var) {
  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return replaceTermInLiteral(lit, o, r);
  }
  SkolemSquashingTermReplacement tr(o,r,var);
  return tr.transform(lit);
}

Formula* InductionContext::getFormula(TermReplacement& tr, bool opposite,
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>>* copy) const
{
  ASS(!_cls.isEmpty());
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>>::Iterator it(_cls);
  Stack<FormulaList*> argLists(1);
  argLists.push(FormulaList::empty());
  while (it.hasNext()) {
    auto cl = it.nextKey();
    auto& st = _cls.get(cl);
    Stack<FormulaList*> temp = argLists;
    argLists.reset();
    for (const auto& kv : st) {
      auto lit = tr.transform(kv.second);
      if (copy) {
        copy->insert(cl, Stack<pair<unsigned,Literal*>>());
        copy->get(cl).push(make_pair(kv.first, lit));
      }
      for (const auto& l : temp) {
        auto lc = FormulaList::copy(l);
        FormulaList::push(new AtomicFormula(opposite ? Literal::complementaryLiteral(lit) : lit), lc);
        argLists.push(lc);
      }
    }
  }
  auto args = FormulaList::empty();
  for (const auto& l : argLists) {
    FormulaList::push(JunctionFormula::generalJunction(opposite ? Connective::OR : Connective::AND, l), args);
  }
  return JunctionFormula::generalJunction(opposite ? Connective::AND : Connective::OR, args);
}

Formula* InductionContext::getFormula(TermList r, bool opposite,
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>>* copy) const
{
  TermReplacement tr(_indTerm, r);
  return getFormula(tr, opposite, copy);
}

Formula* InductionContext::getFormulaWithSquashedSkolems(TermList r, bool opposite,
  unsigned& var, VList** varList, DHMap<Clause*, Stack<pair<unsigned,Literal*>>>* copy) const
{
  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return getFormula(r, opposite, copy);
  }
  SkolemSquashingTermReplacement tr(_indTerm, r, var);
  if (varList) {
    // The variables replacing the Skolems after calling transform
    // are needed for quantification if varList is non-null, collect them
    unsigned temp = var;
    auto res = getFormula(tr, opposite, copy);
    for (unsigned i = temp; i < var; i++) {
      VList::push(i,*varList);
    }
    return res;
  }
  return getFormula(tr, opposite, copy);
}

TermList LiteralSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("LiteralSubsetReplacement::transformSubterm");

  if(trm.isTerm() && trm.term() == _o){
    // Replace either if there are too many occurrences to try all possibilities,
    // or if the bit in _iteration corresponding to this match is set to 1.
    if ((_occurrences > _maxOccurrences) || (1 & (_iteration >> _matchCount++))) {
      return _r;
    }
  }
  return trm;
}

Literal* LiteralSubsetReplacement::transformSubset(InferenceRule& rule) {
  CALL("LiteralSubsetReplacement::transformSubset");
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  // Note: __builtin_popcount() is a GCC built-in function.
  unsigned setBits = __builtin_popcount(_iteration);
  // Skip this iteration if not all bits are set, but more than maxSubset are set.
  while ((_iteration <= _maxIterations) &&
         ((_maxSubsetSize > 0) && (setBits < _occurrences) && (setBits > _maxSubsetSize))) {
    _iteration++;
    setBits = __builtin_popcount(_iteration);
  }
  if ((_iteration >= _maxIterations) ||
      ((_occurrences > _maxOccurrences) && (_iteration > 1))) {
    // All combinations were already returned.
    return nullptr;
  }
  if (setBits == _occurrences) {
    rule = getNonGeneralizedRule(rule);
  } else {
    rule = getGeneralizedRule(rule);
  }
  _matchCount = 0;
  return transform(_lit);
}

List<pair<Literal*, InferenceRule>>* LiteralSubsetReplacement::getListOfTransformedLiterals(InferenceRule rule) {
  CALL("LiteralSubsetReplacement::getListOfTransformedLiterals");

  Literal* l;
  List<pair<Literal*, InferenceRule>>* res = List<pair<Literal*, InferenceRule>>::empty();
  while ((l = transformSubset(rule))) {
    res = List<pair<Literal*, InferenceRule>>::cons(make_pair(l, rule), res);
  }
  return res;
}

Term* getPlaceholderForTerm(Term* t)
{
  CALL("getPlaceholderForTerm");

  OperatorType* ot = env.signature->getFunction(t->functor())->fnType();
  bool added; 
  unsigned placeholderConstNumber = env.signature->addFunction("placeholder_" + ot->toString(), 0, added);
  if (added) {
    env.signature->getFunction(placeholderConstNumber)->setType(OperatorType::getConstantsType(ot->result()));
  }
  return Term::createConstant(placeholderConstNumber);
}

ContextSubsetReplacement::ContextSubsetReplacement(InductionContext context)
  : _context(context), _r(getPlaceholderForTerm(context._indTerm))
{
  unsigned occurrences = 0;
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>>::Iterator it(_context._cls);
  while (it.hasNext()) {
    auto cl = it.nextKey();
    auto& st = _context._cls.get(cl);
    for (const auto& kv : st) {
      occurrences += kv.second->countSubtermOccurrences(TermList(_context._indTerm));
    }
  }
  _maxIterations = pow(2, occurrences);
}

TermList ContextSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("ContextSubsetReplacement::transformSubterm");
  if (trm.isTerm() && trm.term() == _context._indTerm){
    // Replace if the bit in _iteration corresponding to this match is set to 1.
    if (1 & (_iteration >> _matchCount++)) {
      return _r;
    }
  }
  return trm;
}

InductionContext ContextSubsetReplacement::next() {
  CALL("ContextSubsetReplacement::transformSubset");
  ASS(hasNext());
  InductionContext context;
  context._indTerm = _r.term();
  _iteration++;
  _matchCount = 0;
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>>::Iterator it(_context._cls);
  while (it.hasNext()) {
    auto cl = it.nextKey();
    auto& st = _context._cls.get(cl);
    for (const auto& kv : st) {
      auto lit = transform(kv.second);
      if (lit != kv.second) {
        context._cls.insert(cl, Stack<pair<unsigned,Literal*>>());
        context._cls.get(cl).push(make_pair(kv.first, lit));
      }
    }
  }
  return context;
}

void Induction::attach(SaturationAlgorithm* salg) {
  CALL("Induction::attach");

  GeneratingInferenceEngine::attach(salg);
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = static_cast<LiteralIndex*>(_salg->getIndexManager()->request(UNIT_INT_COMPARISON_INDEX));
  }
  if (InductionHelper::isIntInductionTwoOn()) {
    _inductionTermIndex = static_cast<TermIndex*>(_salg->getIndexManager()->request(INDUCTION_TERM_INDEX));
  }
  _structInductionTermIndex = static_cast<TermIndex*>(
    _salg->getIndexManager()->request(STRUCT_INDUCTION_TERM_INDEX));
}

void Induction::detach() {
  CALL("Induction::detach");

  _structInductionTermIndex = nullptr;
  _salg->getIndexManager()->release(STRUCT_INDUCTION_TERM_INDEX);
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = nullptr;
    _salg->getIndexManager()->release(UNIT_INT_COMPARISON_INDEX);
  }
  if (InductionHelper::isIntInductionTwoOn()) {
    _inductionTermIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_TERM_INDEX);
  }
  GeneratingInferenceEngine::detach();
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise, InductionHelper(_comparisonIndex, _inductionTermIndex, _salg->getSplitter()), getOptions(), _structInductionTermIndex));
}

void InductionClauseIterator::processClause(Clause* premise)
{
  CALL("InductionClauseIterator::processClause");

  // The premise should either contain a literal on which we want to apply induction,
  // or it should be an integer constant comparison we use as a bound.
  if (InductionHelper::isInductionClause(premise)) {
    for (unsigned i=0;i<premise->length();i++) {
      processLiteral(premise,(*premise)[i]);
    }
  }
  if (InductionHelper::isIntInductionTwoOn() && InductionHelper::isIntegerComparison(premise)) {
    processIntegerComparison(premise, (*premise)[0]);
  }
}

struct InductionContextFn
{
  InductionContextFn(Clause* premise, Literal* lit) : _premise(premise), _lit(lit) {}

  InductionContext operator()(pair<Term*, VirtualIterator<TermQueryResult>> arg) {
    InductionContext ctx(arg.first, _lit, _premise);
    auto indDepth = _premise->inference().inductionDepth();
    if (indDepth && !env.signature->getFunction(arg.first->functor())->arity()) {
      return ctx;
    }
    while (arg.second.hasNext()) {
      auto tqr = arg.second.next();
      if (_premise == tqr.clause && _lit == tqr.literal) {
        continue;
      }
      if (indDepth && indDepth == tqr.clause->inference().inductionDepth()) {
        if (_lit->functor() != tqr.literal->functor()) {
          continue;
        }
        bool match = false;
        SubtermIterator sti1(_lit);
        SubtermIterator sti2(tqr.literal);
        while (sti1.hasNext()) {
          ASS(sti2.hasNext());
          auto st1 = sti1.next();
          auto st2 = sti2.next();
          if (st1 != st2) {
            if (match || !st1.containsSubterm(st2) || st2.term() != arg.first) {
              match = false;
              break;
            }
            sti1.right();
            sti2.right();
            match = true;
          }
        }
        if (!match) {
          continue;
        }
      }
      ctx._cls.insert(tqr.clause, Stack<pair<unsigned,Literal*>>());
      ctx._cls.get(tqr.clause).push(make_pair(tqr.clause->getLiteralPosition(tqr.literal), tqr.literal));
    }
    return ctx;
  }
private:
  Clause* _premise;
  Literal* _lit;
};

void InductionClauseIterator::processLiteral(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processLiteral");

  if(_opt.showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << lit->toString() << " in " << premise->toString() << endl;
    env.endOutput();
  }

  static bool generalize = _opt.inductionGen();

  if (lit->ground()) {
      Set<Term*> ta_terms;
      Set<Term*> int_terms;
      //TODO this should be a non-variable non-type iterator it seems
      SubtermIterator it(lit);
      while(it.hasNext()){
        TermList ts = it.next();
        if(!ts.isTerm()){ continue; }
        unsigned f = ts.term()->functor(); 
        if(InductionHelper::isInductionTermFunctor(f)){
          if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionFunctor(f)){
            ta_terms.insert(ts.term());
          }
          if(InductionHelper::isIntInductionOneOn() && InductionHelper::isIntInductionTermListInLiteral(ts, lit)){
            int_terms.insert(ts.term());
          }
        }
      }

    if (InductionHelper::isInductionLiteral(lit)) {
      Set<Term*>::Iterator citer1(int_terms);
      while(citer1.hasNext()){
        Term* t = citer1.next();
        Term* indTerm = generalize ? getPlaceholderForTerm(t) : t;
        List<pair<Literal*, InferenceRule>>* indLits = List<pair<Literal*, InferenceRule>>::empty();
        DHMap<Term*, TermQueryResult> grBound;
        addToMapFromIterator(grBound, _helper.getGreaterEqual(t));
        addToMapFromIterator(grBound, _helper.getGreater(t));
        DHMap<Term*, TermQueryResult> leBound;
        addToMapFromIterator(leBound, _helper.getLessEqual(t));
        addToMapFromIterator(leBound, _helper.getLess(t));
        performIntInductionForEligibleBounds(premise, lit, t, indLits, indTerm, /*increasing=*/true, leBound, grBound);
        performIntInductionForEligibleBounds(premise, lit, t, indLits, indTerm, /*increasing=*/false, grBound, leBound);
        List<pair<Literal*, InferenceRule>>::destroy(indLits);
      }
    }
    // collect term queries for each induction term
    auto sideLitsIt = iterTraits(Set<Term*>::Iterator(ta_terms))
      .map([this](Term* arg) {
        return make_pair(arg, _structInductionTermIndex->getGeneralizations(TermList(arg), true));
      });
    // put clauses from queries into contexts alongside with the given clause and induction term
    auto sideLitsIt2 = iterTraits(getMappingIterator(sideLitsIt, InductionContextFn(premise, lit)))
      // filter out that have no "induction literal" or not multi-clause
      .filter([](const InductionContext& arg) {
        return !arg.isSingleLiteral() && arg.hasInductionLiteral();
      });
    // collect contexts for single-literal induction with given clause
    auto indCtxSingle = iterTraits(Set<Term*>::Iterator(ta_terms))
      .map([&lit,&premise](Term* arg) {
        return InductionContext(arg, lit, premise);
      })
      .filter([](const InductionContext& arg) {
        return arg.hasInductionLiteral();
      });
    // generalize all contexts if needed
    auto indCtxIt = iterTraits(getConcatenatedIterator(sideLitsIt2, indCtxSingle))
      .flatMap([](const InductionContext& arg) {
        if (!env.options->inductionGen()) {
          return pvi(getSingletonIterator(arg));
        }
        return vi(new ContextSubsetReplacement(arg));
      });
    while (indCtxIt.hasNext()) {
      auto ctx = indCtxIt.next();
      static bool one = _opt.structInduction() == Options::StructuralInductionKind::ONE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool two = _opt.structInduction() == Options::StructuralInductionKind::TWO ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool three = _opt.structInduction() == Options::StructuralInductionKind::THREE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
      if (ctx.isSingleLiteral()) {
        auto cl = ctx._cls.getOneKey();
        if (!notDone(ctx._cls.get(cl)[0].second, ctx._indTerm)) {
          continue;
        }
      }
      if(one){
        performStructInductionOne(ctx,rule);
      }
      if(two){
        performStructInductionTwo(ctx,rule);
      }
      if(three){
        performStructInductionThree(ctx,rule);
      }
    }
  }
}

void InductionClauseIterator::performIntInductionForEligibleBounds(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, DHMap<Term*, TermQueryResult>& bounds1, DHMap<Term*, TermQueryResult>& bounds2) {
  DHMap<Term*, TermQueryResult>::Iterator it1(bounds1);
  while (it1.hasNext()) {
    TermQueryResult b1 = it1.next();
    // Skip if the premise equals the bound (that would add tautologies to the search space).
    if (b1.clause != premise) {
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it2(bounds2);
        while (it2.hasNext()) {
          TermQueryResult b2 = it2.next();
          if (notDoneInt(origLit, origTerm, increasing, b1.term.term(), b2.term.term(), /*bool fromComparison=*/b1.literal != nullptr)) {
            generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, b1, &b2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(origLit, origTerm, increasing, b1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/b1.literal != nullptr)) {
        generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, b1, nullptr);
      }
    }
  }
  static bool useDefaultBound = _opt.integerInductionDefaultBound();
  if (useDefaultBound && _helper.isInductionForInfiniteIntervalsOn()) {
    static TermQueryResult defaultBound(TermList(theory->representConstant(IntegerConstantType(0))), nullptr, nullptr);
    if (notDoneInt(origLit, origTerm, increasing, defaultBound.term.term(), /*optionalBound2=*/nullptr, /*fromComparison=*/false)) {
      generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, defaultBound, nullptr);
    }
  }
}

void InductionClauseIterator::generalizeAndPerformIntInduction(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, InferenceRule>>*& indLits, Term* indTerm, bool increasing, TermQueryResult& bound1, TermQueryResult* optionalBound2) {
  static bool generalize = _opt.inductionGen();
  // If induction literals were not computed yet, compute them now.
  if (List<pair<Literal*, InferenceRule>>::isEmpty(indLits)) {
    bool finite = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
    InferenceRule rule =
        (bound1.literal == nullptr)
            ? (increasing ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
            : (increasing ? (finite ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM : InferenceRule::INT_INF_UP_INDUCTION_AXIOM)
                          : (finite ? InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));
    if (generalize) {
      Kernel::LiteralSubsetReplacement subsetReplacement(origLit, origTerm, TermList(indTerm), _opt.maxInductionGenSubsetSize());
      indLits = subsetReplacement.getListOfTransformedLiterals(rule);
    } else {
      indLits = new List<pair<Literal*, InferenceRule>>(make_pair(origLit, rule));
    }
  }
  List<pair<Literal*, InferenceRule>>::RefIterator it(indLits);
  while (it.hasNext()) {
    auto& litAndRule = it.next();
    ASS(litAndRule.first != nullptr);
    InductionContext context;
    context._indTerm = indTerm;
    context._cls.insert(premise, { make_pair(premise->getLiteralPosition(origLit), litAndRule.first) });
    performIntInduction(context, litAndRule.second, increasing, bound1, optionalBound2);
  }
}

void InductionClauseIterator::processIntegerComparison(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processIntegerComparison");

  ASS((theory->interpretPredicate(lit) == Theory::INT_LESS) && lit->ground());

  bool positive = lit->isPositive();
  TermList* lesserTL = lit->nthArgument(positive ? 0 : 1);
  TermList* greaterTL = lit->nthArgument(positive ? 1 : 0);
  ASS(lesserTL != nullptr);
  ASS(greaterTL != nullptr);
  Term* lt = lesserTL->term();
  Term* gt = greaterTL->term();
  static bool generalize = _opt.inductionGen();
  DHMap<Term*, TermQueryResult> grBound;
  addToMapFromIterator(grBound, _helper.getGreaterEqual(gt));
  addToMapFromIterator(grBound, _helper.getGreater(gt));
  performIntInductionOnEligibleLiterals(
    gt, generalize ? getPlaceholderForTerm(gt) : gt, _helper.getTQRsForInductionTerm(*greaterTL), /*increasing=*/true, TermQueryResult(*lesserTL, lit, premise), grBound);
  DHMap<Term*, TermQueryResult> leBound;
  addToMapFromIterator(leBound, _helper.getLessEqual(lt));
  addToMapFromIterator(leBound, _helper.getLess(lt));
  performIntInductionOnEligibleLiterals(
    lt, generalize ? getPlaceholderForTerm(lt) : lt, _helper.getTQRsForInductionTerm(*lesserTL), /*increasing=*/false, TermQueryResult(*greaterTL, lit, premise), leBound);
}

void InductionClauseIterator::performIntInductionOnEligibleLiterals(Term* origTerm, Term* indTerm, TermQueryResultIterator inductionTQRsIt, bool increasing, TermQueryResult bound1, DHMap<Term*, TermQueryResult>& bounds2) {
  while (inductionTQRsIt.hasNext()) {
    TermQueryResult tqr = inductionTQRsIt.next();
    // Skip if the TQR clause is equal to the bound clause (that would add tautologies to the search space).
    if (bound1.clause != tqr.clause) {
      // We need to pass an empty list, which will get populated when performing induction.
      // Then we need to destroy it.
      List<pair<Literal*, InferenceRule>>* indLits = List<pair<Literal*, InferenceRule>>::empty();
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it(bounds2);
        while (it.hasNext()) {
          TermQueryResult bound2 = it.next();
          if (notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), bound2.term.term(), /*bool fromComparison=*/bound1.literal != nullptr)) {
            generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, indTerm, increasing, bound1, &bound2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/bound1.literal != nullptr)) {
        generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, indTerm, increasing, bound1, nullptr);
      }
      List<pair<Literal*, InferenceRule>>::destroy(indLits);
    }
  }
}

bool contains(Literal* lit, const DHMap<Clause*, Stack<pair<unsigned, Literal*>>>& toResolve) {
  DHMap<Clause*, Stack<pair<unsigned, Literal*>>>::Iterator it(toResolve);
  while (it.hasNext()) {
    auto cl = it.nextKey();
    const auto& st = toResolve.get(cl);
    for (const auto& kv : st) {
      if (kv.second==lit) {
        return true;
      }
    }
    // TODO check that no other element contains this
  }
  return false;
}

Clause* resolveClauses(const DHMap<Clause*, Stack<pair<unsigned, Literal*>>>& toResolve, const Stack<Clause*>& cls, IntUnionFind::ElementIterator eIt, RobSubstitution* subst)
{
  CALL("resolveClauses");
  ASS(eIt.hasNext());
  auto cl = cls[eIt.next()];
  unsigned newLength = cl->length();
  auto premises = UnitList::singleton(cl);
  while (eIt.hasNext()) {
    auto other = cls[eIt.next()];
    ASS_EQ(other->length(),newLength);
    UnitList::push(other,premises);
  }

  DHMap<Clause*, Stack<pair<unsigned, Literal*>>>::Iterator it(toResolve);
  while (it.hasNext()) {
    auto other = it.nextKey();
    const auto& st = toResolve.get(other);
    newLength += other->length() - st.size() - 1;
    UnitList::push(other, premises);
  }

  Inference inf(GeneratingInferenceMany(InferenceRule::RESOLUTION, premises));
  Clause* res = new(newLength) Clause(newLength, inf);

  unsigned next = 0;
  for(unsigned i=0;i<cl->length();i++) {
    Literal* curr=(*cl)[i];
    if (!contains(Literal::complementaryLiteral(curr), toResolve)) {
      ASS(next < newLength);
      (*res)[next] = subst ? subst->apply(curr, 0) : curr;
      next++;
    }
  }

  DHMap<Clause*, Stack<pair<unsigned, Literal*>>>::Iterator it2(toResolve);
  while (it2.hasNext()) {
    auto other = it2.nextKey();
    const auto& st = toResolve.get(other);
    for (unsigned i = 0; i < other->length(); i++) {
      Literal* curr = (*other)[i];
      bool copyCurr = true;
      for (const auto& kv : st) {
        if (kv.first == i) {
          copyCurr = false;
          break;
        }
      }
      if (copyCurr) {
        (*res)[next] = curr;
        next++;
      }
    }
  }
  ASS_EQ(next,newLength);

  env.statistics->resolution++;
  return res;
}

IntUnionFind findDistributedVariants(const Stack<Clause*>& clauses, const DHMap<Clause*, Stack<pair<unsigned, Literal*>>>& toResolve)
{
  IntUnionFind uf(clauses.size());
  for (unsigned i = 0; i < clauses.size(); i++) {
    auto cl1 = clauses[i];
    for (unsigned k = 0; k < cl1->length(); k++) {
      auto clit = Literal::complementaryLiteral((*cl1)[k]);
      bool found = false;
      unsigned index;
      DHMap<Clause*, Stack<pair<unsigned, Literal*>>>::Iterator mIt(toResolve);
      while (mIt.hasNext()) {
        auto cl = mIt.nextKey();
        const auto& st = toResolve.get(cl);
        if (st.size() > 1) {
          for (const auto& kv : st) {
            if (kv.second == clit) {
              found = true;
              index = k;
              break;
            }
          }
        }
      }
      if (!found) {
        continue;
      }
      for (unsigned j = i+1; j < clauses.size(); j++) {
        auto cl2 = clauses[j];
        bool variant = true;
        for (unsigned l = 0; l < cl1->length(); l++) {
          if ((l == index && cl1->contains((*cl2)[l])) ||
              (l != index && !cl1->contains((*cl2)[l])))
          {
            variant = false;
            break;
          }
        }
        if (variant) {
          uf.doUnion(i,j);
        }
      }
    }
  }
  uf.evalComponents();
  return uf;
}

void InductionClauseIterator::produceClauses(Formula* hypothesis, InferenceRule rule, const DHMap<Clause*, Stack<pair<unsigned, Literal*>>>& toResolve, RobSubstitution* subst)
{
  CALL("InductionClauseIterator::produceClauses");
  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  unsigned maxInductionDepth = 0;
  DHMap<Clause*, Stack<pair<unsigned, Literal*>>>::Iterator it(toResolve);
  while (it.hasNext()) {
    auto cl = it.nextKey();
    maxInductionDepth = max(maxInductionDepth,cl->inference().inductionDepth());
  }
  inf.setInductionDepth(maxInductionDepth+1);
  FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  // Now, when possible, perform resolution against all literals from toResolve, which contain:
  // 1. the original literal,
  // 2. the bounds on the induction term (which are in the form "term < bound", or other comparison),
  // if hyp_clauses contain the literal(s).
  // (If hyp_clauses do not contain the literal(s), the clause is a definition from clausification
  // and just keep it as it is.)
  auto uf = findDistributedVariants(hyp_clauses, toResolve);
  IntUnionFind::ComponentIterator cit(uf);
  while(cit.hasNext()){
    IntUnionFind::ElementIterator eIt = cit.next();
    _clauses.push(resolveClauses(toResolve, hyp_clauses, eIt, subst));
  }
  env.statistics->induction++;
  if (rule == InferenceRule::GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM) {
    env.statistics->generalizedInduction++;
  }
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      env.statistics->structInduction++;
      break;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBInduction++;
      break;
    default:
      ;
  }
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intInfUpInduction++;
      break;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfDownInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intFinUpInduction++;
      break;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinDownInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intDBUpInduction++;
      break;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBDownInduction++;
      break;
    default:
      ;
  }
}

// Given a literal ~L[term], where 'term' is of the integer sort,
// introduce and induction hypothesis for integers, for example:
//   (L[b1] & (![X] : (b1 <= X & X < b2 & L[X]) -> L[x+1])) -> (![Y] : (b1 <= Y & Y <= b2) -> L[Y])
// In general, the hypothesis is an instance of one of the following
// hypotheses (depending on the value of 'increasing'):
//   (L[b1] & (![X] : (interval_x(X)) -> L[x+1])) -> (![Y] : interval_y(Y) -> L[Y])
//   (L[b1] & (![X] : (interval_x(X)) -> L[x-1])) -> (![Y] : interval_y(Y) -> L[Y])
// where 'b1' is bound1.term, and the predicates inteval_x(X) and interval_y(Y)
// capture the property "X (or Y) belongs to the interval [b1, b2] or [b1, b2)",
// where 'b2' is either optionalBound2->term (if present) or depending on 'increasing'
// either infinity or -infinity. (The intervals are set such that the hypothesis
// is valid: if interval_y(Y) holds for some Y, then either interval_x(Y) holds,
// or depending on 'increasing' either interval_x(Y-1) or interval_x(Y+1) holds.)
void InductionClauseIterator::performIntInduction(const InductionContext& context, InferenceRule rule, bool increasing, const TermQueryResult& bound1, TermQueryResult* optionalBound2)
{
  CALL("InductionClauseIterator::performIntInduction");

  TermList b1(bound1.term);
  TermList one(theory->representConstant(IntegerConstantType(increasing ? 1 : -1)));

  TermList x(0,false);
  TermList y(1,false);

  // create L[b1]
  Formula* Lb1 = context.getFormula(b1,true);

  // create L[X]
  Formula* Lx = context.getFormula(x,true);

  // create L[Y]
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>> toResolve;
  Formula* Ly = context.getFormula(y,true,&toResolve);

  // create L[X+1] or L[X-1]
  TermList fpo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),x,one));
  Formula* Lxpo = context.getFormula(fpo,true);

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  // create X>=b1 (which is ~X<b1) or X<=b1 (which is ~b1<X)
  Formula* Lxcompb1 = new AtomicFormula(Literal::create2(less,false,(increasing ? x : b1),(increasing ? b1 : x)));
  // create Y>=b1 (which is ~Y<b1), or Y>b1, or Y<=b1 (which is ~b1<Y), or Y<b1
  // This comparison is mirroring the structure of bound1.literal, which is "b1 <comparison> inductionTerm".
  // If bound1.literal is nullptr, we are using the default bound with the comparison sign >= or <=.
  const bool isBound1Equal = (!bound1.literal || (bound1.literal->functor() == less && bound1.literal->isNegative()));
  const bool isBound1FirstArg = (increasing != isBound1Equal);
  Formula* Lycompb1 = new AtomicFormula(Literal::create2(
        less, !isBound1Equal, (isBound1FirstArg ? b1 : y), (isBound1FirstArg ? y : b1)));

  Formula* FxInterval;
  Formula* FyInterval;
  const bool isDefaultBound = ((bound1.clause == nullptr) || (bound1.literal == nullptr));
  const bool hasBound2 = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
  // Also resolve the hypothesis with comparisons with bound(s) (if the bound(s) are present/not default).
  if (!isDefaultBound) {
    toResolve.insert(bound1.clause, { make_pair(bound1.clause->getLiteralPosition(bound1.literal), Lycompb1->literal()) });
  }
  if (hasBound2) {
    // Finite interval induction, use two bounds on both x and y.
    rule = getFinRule(rule);
    TermList b2(optionalBound2->term);
    // create X<b2 or X>b2 (which is b2<X)
    Formula* Lxcompb2 = new AtomicFormula(Literal::create2(less, true, (increasing ? x : b2), (increasing ? b2 : x)));
    const bool isBound2Equal = (optionalBound2->literal->functor() == less && optionalBound2->literal->isNegative());
    const bool isBound2FirstArg = (increasing == isBound2Equal);
    // create Y<b2, or Y<=b2 (which is ~b2<Y) or Y>b2, or Y>=b2 (which is ~Y<b2)
    Formula* Lycompb2 = new AtomicFormula(Literal::create2(
          less, !isBound2Equal, (isBound2FirstArg ? b2 : y), (isBound2FirstArg ? y : b2)));
    FxInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lxcompb1, FormulaList::singleton(Lxcompb2)));
    FyInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lycompb1, FormulaList::singleton(Lycompb2)));
    if (!isDefaultBound) {
      // If there is also a second bound, add that to the list as well.
      toResolve.insert(optionalBound2->clause,
        { make_pair(optionalBound2->clause->getLiteralPosition(optionalBound2->literal), Lycompb2->literal()) });
    }
  } else {
    // Infinite interval induction (either with default bound or not), use only one bound on both x and y.
    if (isDefaultBound) rule = getDBRule(rule);
    else rule = getInfRule(rule);
    FxInterval = Lxcompb1;
    FyInterval = Lycompb1;
  }

  // Create the hypothesis, with FxInterval and FyInterval being as described
  // in the comment above this function.
  Formula* hyp = new BinaryFormula(Connective::IMP,
                   new JunctionFormula(Connective::AND,FormulaList::cons(Lb1,FormulaList::singleton(
                     Formula::quantify(new BinaryFormula(Connective::IMP,
                       new JunctionFormula(Connective::AND, FormulaList::cons(FxInterval,FormulaList::singleton(Lx))),
                       Lxpo))))),
                   Formula::quantify(new BinaryFormula(Connective::IMP,FyInterval,Ly)));

  RobSubstitution subst;
  if (isDefaultBound) {
    ALWAYS(subst.match(y,0,TermList(context._indTerm),1));
  }

  produceClauses(hyp, rule, toResolve, isDefaultBound ? &subst : nullptr);
}

/**
 * Introduce the Induction Hypothesis
 * ( L[base1] & ... & L[basen] & (L[x] => L[c1(x)]) & ... (L[x] => L[cm(x)]) ) => L[x]
 * for some lit ~L[a]
 * and then force binary resolution on L for each resultant clause
 */

void InductionClauseIterator::performStructInductionOne(const InductionContext& context, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionOne"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  FormulaList* formulas = FormulaList::empty();

  unsigned var = 0;

  // first produce the formula
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
      Stack<TermList> argTerms;
      Stack<TermList> ta_vars;
      for(unsigned j=0;j<arity;j++){
        TermList x(var,false);
        var++;
        if(con->argSort(j) == ta_sort){
          ta_vars.push(x);
        }
        argTerms.push(x);
      }
      // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
      auto right = context.getFormulaWithSquashedSkolems(
        TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())), true, var);
      FormulaList* args = FormulaList::empty();
      Stack<TermList>::Iterator tvit(ta_vars);
      while(tvit.hasNext()){
        auto hypVars = VList::empty();
        auto hyp = context.getFormulaWithSquashedSkolems(tvit.next(),true,var,&hypVars);
        // quantify each hypotheses with variables replacing Skolems explicitly
        if (hypVars) {
          hyp = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), hyp);
        }
        FormulaList::push(hyp,args);
      }

      FormulaList::push(args ?
        new BinaryFormula(Connective::IMP,JunctionFormula::generalJunction(Connective::AND,args),right) : right, formulas);
  }
  ASS(formulas);
  Formula* indPremise = JunctionFormula::generalJunction(Connective::AND,formulas);
  DHMap<Clause*, Stack<pair<unsigned,Literal*>>> toResolve;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++,false), true, var, nullptr, &toResolve);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(indPremise),
                            Formula::quantify(conclusion));

  produceClauses(hypothesis, rule, toResolve);
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * We produce the clause ~L[x] \/ ?y : L[y] & !z (z subterm y -> ~L[z])
 * and perform resolution with lit L[c]
 */
void InductionClauseIterator::performStructInductionTwo(const InductionContext& context, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionTwo"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  // make L[y]
  TermList y(0,false); 
  unsigned var = 1;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  auto Ly = context.getFormulaWithSquashedSkolems(y,false,var,&mainVars);

  // for each constructor and destructor make
  // ![Z] : y = cons(Z,dec(y)) -> ( ~L[dec1(y)] & ~L[dec2(y)]
  FormulaList* formulas = FormulaList::empty();

  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
  
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
        }
      }
      ASS(taTerms.isNonEmpty());
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        TermList djy = tit.next();
        auto hypVars = VList::empty();
        auto f = context.getFormulaWithSquashedSkolems(djy,true,var,&hypVars);
        if (hypVars) {
          f = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), f);
        }
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));
      FormulaList::push(imp,formulas);
    }
  }
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                        formulas ? new JunctionFormula(Connective::AND,FormulaList::cons(Ly,formulas))
                                 : Ly);

  DHMap<Clause*, Stack<pair<unsigned,Literal*>>> toResolve;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++, false), true, var, nullptr, &toResolve);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  produceClauses(hypothesis, rule, toResolve);
}

/*
 * A variant of Two where we are stronger with respect to all subterms. here the existential part is
 *
 * ?y : L[y] &_{con_i} ( y = con_i(..dec(y)..) -> smaller(dec(y))) 
             & (!x : smallerThanY(x) -> smallerThanY(destructor(x))) 
             & !z : smallerThanY(z) => ~L[z]
 *
 * i.e. we add a new special predicat that is true when its argument is smaller than Y
 *
 */
void InductionClauseIterator::performStructInductionThree(const InductionContext& context, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionThree");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(context._indTerm->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  // make L[y]
  TermList x(0,false); 
  TermList y(1,false); 
  TermList z(2,false); 
  unsigned vars = 3;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  auto Ly = context.getFormulaWithSquashedSkolems(y,false,vars,&mainVars);

  // make smallerThanY
  unsigned sty = env.signature->addFreshPredicate(1,"smallerThan");
  env.signature->getPredicate(sty)->setType(OperatorType::getPredicateType({ta_sort}));

  // make ( y = con_i(..dec(y)..) -> smaller(dec(y)))  for each constructor 
  FormulaList* conjunction = FormulaList::singleton(Ly);
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      Stack<unsigned> ta_vars;
      Stack<TermList> varTerms;
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        TermList xj(vars,false);
        varTerms.push(xj);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
          ta_vars.push(vars);
        }
        vars++;
      }
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);

      // create smaller(cons(x1,..,xn))
      Formula* smaller_coni = new AtomicFormula(Literal::create1(sty,true,
                                TermList(Term::create(con->functor(),(unsigned)varTerms.size(),varTerms.begin()))));

      FormulaList* smallers = FormulaList::empty();
      Stack<unsigned>::Iterator vtit(ta_vars);
      while(vtit.hasNext()){
        FormulaList::push(new AtomicFormula(Literal::create1(sty,true,TermList(vtit.next(),false))),smallers);
      }
      ASS(smallers);
      Formula* ax = Formula::quantify(new BinaryFormula(Connective::IMP,smaller_coni,
                      JunctionFormula::generalJunction(Connective::AND,smallers)));

      // now create a conjunction of smaller(d(y)) for each d
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        Formula* f = new AtomicFormula(Literal::create1(sty,true,tit.next()));
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));

      FormulaList::push(imp,conjunction);
      FormulaList::push(ax,conjunction);
    } 
  }
  // now !z : smallerThanY(z) => ~L[z]
  Formula* smallerImpNL = Formula::quantify(new BinaryFormula(Connective::IMP, 
                            new AtomicFormula(Literal::create1(sty,true,z)),
                            context.getFormulaWithSquashedSkolems(z,true,vars)));

  FormulaList::push(smallerImpNL,conjunction);
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                       new JunctionFormula(Connective::AND,conjunction));

  DHMap<Clause*, Stack<pair<unsigned,Literal*>>> toResolve;
  auto conclusion = context.getFormulaWithSquashedSkolems(x,true,vars,nullptr,&toResolve);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  produceClauses(hypothesis, rule, toResolve);
}

bool InductionClauseIterator::notDone(Literal* lit, Term* term)
{
  CALL("InductionClauseIterator::notDone");

  static DHSet<Literal*> done;
  static LiteralSubstitutionTree lis(false);
  static DHMap<TermList,TermList> blanks;
  const bool strengthenHyp = _opt.inductionStrengthenHypothesis();
  TermList srt = env.signature->getFunction(term->functor())->fnType()->result();

  if(!blanks.find(srt)){
    unsigned fresh = env.signature->addFreshFunction(0,"blank");
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    TermList blank = TermList(Term::createConstant(fresh));
    blanks.insert(srt,blank);
  }

  unsigned var = 0;
  Literal* rep = replaceTermAndSquashSkolemsInLiteral(lit,term,blanks.get(srt),var);
  // If we strengthen the literal there might be an arbitrary number of
  // induction terms apart from the main one, so it is easier to replace
  // the rest with variables and check for variants in an index.
  // Otherwise there is only one term to replace and it gives a unique
  // literal, so a pointer check is sufficient.
  if (strengthenHyp) {
    if (lis.getVariants(rep, false, false).hasNext()) {
      return false;
    }

    lis.insert(rep, nullptr);
  } else {
    if(done.contains(rep)){
      return false;
    }

    done.insert(rep);
  }

  return true;
}

// Note: only works for unit clauses.
// TODO: encapsulate the 'done' map in a helper class to have it deallocate correctly.
bool InductionClauseIterator::notDoneInt(Literal* lit, Term* t, bool increasing, Term* bound1, Term* optionalBound2, bool fromComparison)
{
  CALL("InductionClauseIterator::notDoneInt");

  // Map structure:
  // (induction lit/t representation, increasing) -> ((bound1, optionalBound2) -> (existsFromComparisonTrue, {(induction term, fromComparison)}))
  static DHMap<pair<Literal*, bool>, DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>*> done;

  // Create representation of lit/t combination
  static Term* blank;
  static unsigned freshInt = env.signature->addFreshFunction(0, "blank");
  if (!blank) {
    env.signature->getFunction(freshInt)->setType(OperatorType::getConstantsType(AtomicSort::intSort()));
    blank = Term::createConstant(freshInt);
  }
  Literal* rep = replaceTermInLiteral(lit,t,TermList(blank));

  auto key = make_pair(rep, increasing);
  DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>* val;
  pair<bool, DHMap<Term*, bool>*>* p;
  auto bounds = make_pair(bound1, optionalBound2);
  if (done.find(key, val)) {
    // Check two conditions under which we can skip this induction literal/term/bounds combination:
    p = val->findPtr(bounds);
    if (p != nullptr) {
      // 1. either induction was applied on the same induction literal representation with the same bound(s),
      //    and the bound(s) came from comparison (i.e., its comparison with induction term was resolved away).
      if (p->first) return false;
      // 2. or induction was applied on the same induction literal & induction term with the same bound(s),
      //    and either now the bound did not come from comparison, or then it did.
      bool previousFromComparison = false;
      if (p->second->find(t, previousFromComparison) && (!fromComparison || previousFromComparison)) return false;
    }
    // There is a 3rd possibility: the bound now is an interpreted constant, and induction was applied
    // on the same induction lit and some other interpreted constant bound, which came from comparison,
    // and the bound then was <= this bound (if increasing) or >= this bound (if not increasing).
    // TODO: explore if it is worth it to implement this condition.
  }
  else {
    val = new DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>();
    done.insert(key, val);
  }
  p = val->findPtr(bounds);
  DHMap<Term*, bool>* insideMap;
  if (p != nullptr) {
    insideMap = p->second;
    p->first |= fromComparison;
  } else {
    insideMap = new DHMap<Term*, bool>();
    val->insert(bounds, make_pair(fromComparison, insideMap));
  }
  bool previousFromComparison = false;
  if (!insideMap->find(t, previousFromComparison) || (!previousFromComparison && fromComparison)) {
    insideMap->set(t, fromComparison);
  }

  return true;
}

}
