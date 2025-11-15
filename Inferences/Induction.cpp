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

#include <map>
#include <set>
#include <utility>
#include <vector>

#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Set.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"
#include "Shell/AnswerLiteralManager.hpp"

#include "Induction.hpp"

using std::pair;
using std::make_pair;

#define INDUCTION_CONTEXT_BANK 0
#define INDUCTION_CLAUSE_BANK 1
#define NUM_SPECIAL_BANKS 2

namespace Inferences
{
using namespace std;
using namespace Kernel;
using namespace Lib;

Term* ActiveOccurrenceIterator::next()
{
  Term* t = _stack.pop();
  auto templ = _fnDefHandler.getRecursionTemplate(t);
  auto actPos = templ ? &templ->inductionPositions() : nullptr;
  for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
    if ((!actPos || (*actPos)[i]) && t->nthArgument(i)->isTerm()) {
      _stack.push(t->nthArgument(i)->term());
    }
  }
  return t;
}

Term* getPlaceholderForTerm(const Stack<Term*>& ts, unsigned i)
{
  static DHMap<pair<TermList,unsigned>,Term*> placeholders;
  TermList srt = SortHelper::getResultSort(ts[i]);
  auto p = make_pair(srt,i);
  if(!placeholders.find(p)){
    unsigned fresh = env.signature->addFreshFunction(0,(srt.toString() + "_placeholder" + Int::toString(i)).c_str());
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    auto res = Term::createConstant(fresh);
    placeholders.insert(p,res);
    return res;
  }
  return placeholders.get(p);
}

TermList TermReplacement::transformSubterm(TermList trm)
{
  // if we reach any of the mapped terms,
  // replace it with the term it is mapped to
  if(trm.isTerm() && _m.count(trm.term())){
    return _m.at(trm.term());
  }
  return trm;
}

TermList InductionTermReplacement::transformSubterm(TermList trm)
{
  // if we reach any of the mapped terms,
  // replace it with the term it is mapped to
  if (trm.isVar()) {
    unsigned v;
    if (_renaming.findOrInsert(trm.var(), v, _nextVar)) {
      _nextVar++;
      _renamedFreeVars.insert(v);
    }
    return TermList::var(v);
  }
  if (trm.term()->isSort()) {
    return trm;
  }
  auto t = trm.term();
  auto it = _m.find(t);
  if (it != _m.end()){
    return it->second;
  }
  if (!_squashSkolems || !env.signature->getFunction(t->functor())->skolem()) {
    return trm;
  }
  unsigned* ptr;
  if (_skolemToVarMap.getValuePtr(t, ptr, _nextVar)) {
    _varsReplacingSkolems.insert(_nextVar++);
  }
  return TermList::var(*ptr);
}

void InductionTermReplacement::resetRenaming(RobSubstitution* subst, unsigned bank)
{
  if (subst) {
    for (const auto& [v1,v2] : iterTraits(_renaming.items())) {
      ALWAYS(subst->unify(TermList::var(v1),bank,TermList::var(v2),INDUCTION_CLAUSE_BANK));
    }
  }
  _renaming.reset();
}

VList* InductionTermReplacement::getRenamedFreeVars() const
{
  return VList::fromIterator(iterTraits(_renamedFreeVars.iter()));
}

VList* InductionTermReplacement::getVarsReplacingSkolems() const
{
  return VList::fromIterator(iterTraits(_varsReplacingSkolems.iter()));
}

Formula* InductionContext::getFormula(
  const InductionUnit& unit, const Substitution& typeBinder, unsigned& nextVar, VList** varsReplacingSkolems, RobSubstitution* subst) const
{
  auto hyps = FormulaList::empty();
  for (const auto& lit : unit.conditions) {
    FormulaList::push(new AtomicFormula(SubstHelper::apply(lit, typeBinder)), hyps);
  }
  auto left = hyps ? JunctionFormula::generalJunction(Connective::AND, hyps) : nullptr;
  auto hypVars = VList::fromIterator(unit.condUnivVars.iterFifo());
  if (hypVars) {
    ASS(left);
    left = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), left);
  }

  vector<TermList> ts;
  for (const auto& t : unit.F_terms) {
    ts.push_back(SubstHelper::apply(t, typeBinder));
  }
  auto renamedFreeVars = VList::empty();
  auto right = getFormulaWithSquashedSkolems(ts, nextVar, renamedFreeVars, varsReplacingSkolems, subst);
  auto f = left ? new BinaryFormula(Connective::IMP, left, right) : right;
  if (renamedFreeVars) {
    f = new QuantifiedFormula(Connective::EXISTS, renamedFreeVars, SList::empty(), f);
  }
  return f;
}

Formula* InductionContext::getFormula(InductionTermReplacement& tr, RobSubstitution* subst) const
{
  ASS(_cls.isNonEmpty());
  auto argLists = FormulaList::empty();
  for (unsigned i = 0; i < _cls.size(); i++) {
    auto lits = _cls[i].second;
    auto argList = FormulaList::empty();
    for (const auto& lit : lits) {
      auto tlit = tr.transformLiteral(lit);
      FormulaList::push(new AtomicFormula(Literal::complementaryLiteral(tlit)), argList);
    }
    FormulaList::push(JunctionFormula::generalJunction(Connective::AND, argList), argLists);
    tr.resetRenaming(subst, NUM_SPECIAL_BANKS + i);
  }
  return JunctionFormula::generalJunction(Connective::OR, argLists);
}

Formula* InductionContext::getFormulaWithFreeVar(TermList t, unsigned freeVar, unsigned freeVarSub, RobSubstitution* subst) const
{
  ASS_EQ(_cls.size(),1);
  ASS_EQ(_cls[0].second.size(),1);

  auto replacementMap = getReplacementMap({ t }, subst);
  TermReplacement tr(replacementMap);
  auto tlit = tr.transformLiteral(_cls[0].second[0]);
  auto replaced = new AtomicFormula(Literal::complementaryLiteral(tlit));
  Substitution s;
  s.bindUnbound(freeVar, TermList::var(freeVarSub));
  return SubstHelper::apply(replaced, s);
}

Formula* InductionContext::getFormulaWithSquashedSkolems(
  const std::vector<TermList>& r, unsigned& nextVar, VList*& renamedFreeVars, VList** varsReplacingSkolems, RobSubstitution* subst) const
{
  // Assuming this object is the result of a ContextReplacement (or similar iterator)
  // we can replace the ith placeholder with the ith term in r.
  auto replacementMap = getReplacementMap(r, subst);
  InductionTermReplacement tr(replacementMap, env.options->inductionStrengthenHypothesis(), nextVar);
  auto res = getFormula(tr, subst);
  if (subst) {
    for (const auto& [t,v] : iterTraits(tr._skolemToVarMap.items())) {
      ALWAYS(subst->unify(TermList::var(v),INDUCTION_CLAUSE_BANK,TermList(t),INDUCTION_CONTEXT_BANK));
    }
  }
  renamedFreeVars = tr.getRenamedFreeVars();
  if (varsReplacingSkolems) {
    // The variables replacing the Skolems after calling transform
    // are needed for quantification if varList is non-null, collect them
    *varsReplacingSkolems = tr.getVarsReplacingSkolems();
  }
  return res;
}

unsigned InductionContext::getFreeVariable() const {
  // Note: we return the first free variable from literals of _cls,
  // because we assume there is just one
  for (const auto& kv : _cls) {
    for (const auto& lit : kv.second) {
      VariableIterator vi(lit);
      if (vi.hasNext()) {
        return vi.next().var();
      }
    }
  }
  ASSERTION_VIOLATION;
}

template<typename Fun>
InductionContext InductionContext::transform(Fun fn) const
{
  Stack<std::pair<Clause*, LiteralStack>> cls;
  for (const auto& [cl, lits] : _cls) {
    LiteralStack resLits;
    for (const auto& lit : lits) {
      auto tlit = fn(lit);
      if (tlit && tlit != lit) {
        resLits.push(tlit);
      }
    }
    if (resLits.isEmpty()) {
      continue;
    }
    cls.emplace(cl, std::move(resLits));
  }
  return InductionContext(_indTerms, std::move(cls));
}

std::unordered_map<Term*,TermList> InductionContext::getReplacementMap(const std::vector<TermList>& r, RobSubstitution* subst) const
{
  ASS_EQ(r.size(), _indTerms.size());
  std::unordered_map<Term*,TermList> replacementMap;
  for (unsigned i = 0; i < _indTerms.size(); i++) {
    auto ph = getPlaceholderForTerm(_indTerms,i);
    replacementMap.insert(make_pair(ph,r[i]));
    if (subst) {
      ASS(r[i].isVar());
      ALWAYS(subst->unify(r[i],INDUCTION_CLAUSE_BANK,TermList(ph),INDUCTION_CONTEXT_BANK));
    }
  }
  return replacementMap;
}

std::unordered_map<Term*,TermList> getContextReplacementMap(const InductionContext& context, bool inverse = false)
{
  std::unordered_map<Term*,TermList> m;
  for (unsigned i = 0; i < context._indTerms.size(); i++) {
    auto ph = getPlaceholderForTerm(context._indTerms,i);
    m.insert(make_pair(inverse ? ph : context._indTerms[i], inverse ? context._indTerms[i] : ph));
  }
  return m;
}

ContextReplacement::ContextReplacement(const InductionContext& context)
    : TermReplacement(getContextReplacementMap(context)),
      _context(context), _used(false) {}

InductionContext ContextReplacement::next()
{
  ASS(hasNext());
  _used = true;
  return _context.transform([&](Literal* lit) {
    return transformLiteral(lit);
  });
}

ActiveOccurrenceContextReplacement::ActiveOccurrenceContextReplacement(
  const InductionContext& context, const FunctionDefinitionHandler& fnDefHandler)
  : ContextReplacement(context),
    _fnDefHandler(fnDefHandler),
    _iteration(_context._indTerms.size(),0),
    _matchCount(_context._indTerms.size(),0),
    _hasNonActive(false)
{}

TermList ActiveOccurrenceContextReplacement::transformSubterm(TermList trm)
{
  if (trm.isTerm()) {
    auto it = std::find(_context._indTerms.begin(), _context._indTerms.end(), trm.term());
    if (it != _context._indTerms.end()) {
      auto i = it - _context._indTerms.begin();
      if (1 & (_iteration[i] >> _matchCount[i]++)) {
        return _m.at(trm.term());
      }
    }
  }
  return trm;
}

InductionContext ActiveOccurrenceContextReplacement::next()
{
  ASS(hasNext());
  _used = true;
  return _context.transform([&](Literal* lit) {
    for (unsigned i = 0; i < _iteration.size(); i++) {
      _iteration[i] = 0;
      _matchCount[i] = 0;
    }
    Stack<pair<Term*,bool>> stack(8);
    stack.push({ lit, true });
    while (stack.isNonEmpty()) {
      auto [t,active] = stack.pop();
      auto templ = _fnDefHandler.getRecursionTemplate(t);
      for (unsigned k = 0; k < t->arity(); k++) {
        if (t->nthArgument(k)->isTerm()) {
          stack.push({ t->nthArgument(k)->term(),
            active && templ ? templ->inductionPositions()[k] : active });
        }
      }
      if (t->ground()) {
        auto it = std::find(_context._indTerms.begin(), _context._indTerms.end(), t);
        if (it != _context._indTerms.end()) {
          auto idx = it - _context._indTerms.begin();
          _iteration[idx] = (_iteration[idx] << 1) | active;
          if (!active) {
            _hasNonActive = true;
          }
        }
      }
    }
    return transformLiteral(lit);
  });
}

VirtualIterator<InductionContext> contextReplacementInstance(const InductionContext& context, const Options& opt, FunctionDefinitionHandler& fnDefHandler)
{
  auto ctx = context;
  auto res = VirtualIterator<InductionContext>::getEmpty();
  if (opt.inductionOnActiveOccurrences()) {
    // In case of using active occurrences, we replace the input
    // context with one where the active occurrences are already
    // replaced, so that we only iterate on the rest of them below.
    ActiveOccurrenceContextReplacement aor(context, fnDefHandler);
    ASS(aor.hasNext());
    auto ao_ctx = aor.next();
    // If there are no active occurrences, we get an empty context
    // and we simply fall back to inducting on all occurrences.
    //
    // TODO do this filtering inside ActiveOccurrenceContextReplacement
    if (ao_ctx._cls.isNonEmpty()) {
      ctx = ao_ctx;
      res = pvi(getSingletonIterator(ctx));
      if (!aor.hasNonActive()) {
        return res;
      }
    }
  }
  return pvi(concatIters(res, vi(opt.inductionGen()
    ? new ContextSubsetReplacement(ctx, opt.maxInductionGenSubsetSize())
    : new ContextReplacement(ctx))));
}

ContextSubsetReplacement::ContextSubsetReplacement(const InductionContext& context, const unsigned maxSubsetSize)
  : ContextReplacement(context),
    _iteration(context._indTerms.size(),1), // we want to exclude empty subset, so set all to 1
    _maxIterations(context._indTerms.size(),0),
    _matchCount(context._indTerms.size(),0),
    _maxSubsetSize(maxSubsetSize),
    _ready(false), _done(false)
{
  for (unsigned i = 0; i < _context._indTerms.size(); i++) {
    unsigned occurrences = 0;
    for (const auto& kv : _context._cls) {
      for (const auto& lit : kv.second) {
        occurrences += lit->countSubtermOccurrences(TermList(_context._indTerms[i]));
      }
    }
    _maxIterations[i] = pow(2, occurrences);
    if (_maxIterations[i] > _maxOccurrences) {
      _iteration[i] = _maxIterations[i]-1;
    }
  }
  // find first iteration that shouldn't be skipped
  while (!_done && shouldSkipIteration()) {
    stepIteration();
  }
  _ready = true;
}

TermList ContextSubsetReplacement::transformSubterm(TermList trm)
{
  if (trm.isTerm()) {
    auto it = std::find(_context._indTerms.begin(), _context._indTerms.end(), trm.term());
    if (it != _context._indTerms.end()) {
      auto i = it - _context._indTerms.begin();
      if (1 & (_iteration[i] >> _matchCount[i]++)) {
        return _m.at(trm.term());
      }
    }
  }
  return trm;
}

bool ContextSubsetReplacement::hasNext()
{
  if (_ready) {
    return !_done;
  }
  _ready = true;
  // we step forward until we find an
  // iteration which shouldn't be skipped
  // or we run out of iterations
  do {
    stepIteration();
  } while (!_done && shouldSkipIteration());

  return !_done;
}

InductionContext ContextSubsetReplacement::next()
{
  ASS(_ready);
  for (unsigned i = 0; i < _context._indTerms.size(); i++) {
    _matchCount[i] = 0;
  }
  _ready = false;
  return _context.transform([&](Literal* lit) -> Literal* {
    auto tlit = transformLiteral(lit);
    // check if tlit has placeholders
    for (unsigned i = 0; i < _context._indTerms.size(); i++) {
      if (tlit->containsSubterm(TermList(getPlaceholderForTerm(_context._indTerms,i)))) {
        return tlit;
      }
    }
    return nullptr;
  });
}

bool ContextSubsetReplacement::shouldSkipIteration() const
{
  // We skip an iteration if too many (but not all)
  // occurrences of an induction term are used.
  const bool subsetSizeCheck = _maxSubsetSize > 0;
  for (unsigned i = 0; i < _iteration.size(); i++) {
    unsigned setBits = __builtin_popcount(_iteration[i]);
    // never skip no generalization
    if (_iteration[i] == _maxIterations[i]-1) {
      continue;
    }
    if (subsetSizeCheck && setBits > _maxSubsetSize) {
      return true;
    }
  }
  return false;
}

void ContextSubsetReplacement::stepIteration()
{
  for (unsigned i = 0; i < _iteration.size(); i++) {
    if (_maxIterations[i] > _maxOccurrences) {
      continue;
    }
    _iteration[i]++;
    if (_iteration[i] < _maxIterations[i]) {
      return;
    } else {
      _iteration[i] = 1;
    }
  }
  _done = true;
}

void Induction::attach(SaturationAlgorithm* salg) {
  GeneratingInferenceEngine::attach(salg);
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = static_cast<LiteralIndex<LiteralClause>*>(_salg->getIndexManager()->request(UNIT_INT_COMPARISON_INDEX));
    _inductionTermIndex = static_cast<TermIndex*>(_salg->getIndexManager()->request(INDUCTION_TERM_INDEX));
  }
  if (InductionHelper::isNonUnitStructInductionOn()) {
    _structInductionTermIndex = static_cast<TermIndex*>(
      _salg->getIndexManager()->request(STRUCT_INDUCTION_TERM_INDEX));
  }
}

void Induction::detach() {
  if (InductionHelper::isNonUnitStructInductionOn()) {
    _structInductionTermIndex = nullptr;
    _salg->getIndexManager()->release(STRUCT_INDUCTION_TERM_INDEX);
  }
  if (InductionHelper::isIntInductionOn()) {
    _comparisonIndex = nullptr;
    _salg->getIndexManager()->release(UNIT_INT_COMPARISON_INDEX);
    _inductionTermIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_TERM_INDEX);
  }
  GeneratingInferenceEngine::detach();
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  return pvi(InductionClauseIterator(premise, InductionHelper(_comparisonIndex, _inductionTermIndex),
    _salg, _structInductionTermIndex, _formulaIndex));
}

void InductionClauseIterator::processClause(Clause* premise)
{
  // The premise should either contain a literal on which we want to apply induction,
  // or it should be an integer constant comparison we use as a bound.
  if (InductionHelper::isInductionClause(premise)) {
    for (Literal* lit : premise->iterLits()) {
      if (!lit->isAnswerLiteral()) {
        processLiteral(premise, lit);
      }
    }
  }
  if (InductionHelper::isIntInductionOn() && InductionHelper::isIntegerComparison(premise)) {
    processIntegerComparison(premise, (*premise)[0]);
  }
}

/**
 * This class implements two heuristics for selecting multiple literals for induction.
 * 1. Induction depth is 0 for all premises, so we should have essentially input
 *    clauses or their descendants in the induction, directly from the conjecture.
 *    TODO: AVATAR compoenents also have induction depth 0, this makes the heuristic
 *          a bit more prolific than intended.
 * 2. Induction depth is d(>0) for all premises, each premise gives exactly one
 *    literal to induct on and each literal has the same topmost (non-equality)
 *    predicate symbol. Additionally, there is one literal p(t1,...t,...,tn) s.t. all
 *    others are of the form [~]p(t1,...,t',...tn) and t' is a subterm of t.
 *    The rationale behind this is that many inductions on predicate symbols get stuck
 *    without the induction hypothesis being applicable, this resolves some of them,
 *    when we induct on t', getting rid of it in both the conclusion and hypotheses.
 *    This is mostly useful when t' is not a constant, so we check for that too.
 */
struct InductionContextFn
{
  InductionContextFn(Clause* premise, Literal* lit) : _premise(premise), _lit(lit) {}

  VirtualIterator<InductionContext> operator()(pair<Stack<Term*>, VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>> arg) {
    auto indDepth = _premise->inference().inductionDepth();
    // heuristic 2
    if (indDepth) {
      auto res = VirtualIterator<InductionContext>::getEmpty();
      // TODO make this work for multiple induction terms
      ASS(arg.first.isNonEmpty());
      if (arg.first.size() > 1) {
        return res;
      }
      auto indTerm = arg.first[0];
      // check for complex term and non-equality
      if (_lit->isEquality() || !indTerm->arity()) {
        return res;
      }
      while (arg.second.hasNext()) {
        auto& tqr = *arg.second.next().data;
        if (indDepth != tqr.clause->inference().inductionDepth()) {
          continue;
        }
        // check for different clauses and same topmost functors
        if (tqr.clause == _premise || _lit->functor() != tqr.literal->functor()) {
          continue;
        }
        bool match = false;
        SubtermIterator sti1(_lit);
        SubtermIterator sti2(tqr.literal);
        while (sti1.hasNext()) {
          ALWAYS(sti2.hasNext());
          auto st1 = sti1.next();
          auto st2 = sti2.next();
          if (st1 != st2) {
            // if the two terms are not equal, we check that
            // - no other non-equal pair of terms have been processed (match)
            // - one of them contains the other and the contained one is the induction term
            if (match ||
              !((st1.containsSubterm(st2) && st2.term() == indTerm) ||
                (st2.containsSubterm(st1) && st1.term() == indTerm)))
            {
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
        InductionContext ctx(arg.first, {
          { _premise, { _lit } },
          { tqr.clause, { tqr.literal } }
        });
        res = pvi(concatIters(res, getSingletonIterator(ctx)));
      }
      return res;
    // heuristic 1
    } else {
      std::unordered_map<Clause*, LiteralStack> clauseLitMap;
      clauseLitMap.insert({ _premise, { _lit } });
      Set<Literal*,SharedTermHash> lits;
      lits.insert(_lit);
      while (arg.second.hasNext()) {
        auto& tqr = *arg.second.next().data;
        // TODO: having the same literal multiple times or its complement has unwanted effects
        // in the clausification/resolution part, so avoid it for now
        if (lits.contains(tqr.literal) || lits.contains(Literal::complementaryLiteral(tqr.literal))) {
          continue;
        }
        lits.insert(tqr.literal);
        if (indDepth != tqr.clause->inference().inductionDepth()) {
          continue;
        }
        clauseLitMap.emplace(tqr.clause, LiteralStack()).first->second.push(tqr.literal);
      }
      Stack<std::pair<Clause*, LiteralStack>> cls;
      for (const auto& kv : clauseLitMap) {
        cls.push(kv);
      }
      return pvi(getSingletonIterator(InductionContext(arg.first, std::move(cls))));
    }
  }
private:
  Clause* _premise;
  Literal* _lit;
};

void InductionClauseIterator::processLiteral(Clause* premise, Literal* lit)
{
  if(_opt.showInduction()){
    std::cout << "[Induction] process " << lit->toString() << " in " << premise->toString() << endl;
  }

  if (_opt.inductionGroundOnly() && !lit->ground()) {
    return;
  }

  if (_opt.questionAnswering() != Options::QuestionAnsweringMode::SYNTHESIS) {
    Set<Term*,SharedTermHash> int_terms;
    typedef std::set<const InductionTemplate*> TemplateTypeArgsSet;
    std::map<Stack<Term*>,TemplateTypeArgsSet> ta_terms;

    VirtualIterator<Term*> it;
    if (_opt.inductionOnActiveOccurrences()) {
      it = vi(new ActiveOccurrenceIterator(lit, _fnDefHandler));
    } else {
      it = vi(new NonVariableNonTypeIterator(lit, /*includeSelf=*/true));
    }
    for (const auto& t : iterTraits(it)) {
      if (!t->isLiteral() && InductionHelper::isInductionTerm(t)){
        if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionTerm(t)){
          ta_terms.emplace(Stack<Term*>{ t }, TemplateTypeArgsSet());
        }
        if(InductionHelper::isIntInductionOn() && InductionHelper::isIntInductionTermListInLiteral(t, lit)){
          int_terms.insert(t);
        }
      }
      Stack<Term*> indTerms;
      auto templ = _fnDefHandler.matchesTerm(t, indTerms);
      if (templ) {
        auto it = ta_terms.emplace(std::move(indTerms), TemplateTypeArgsSet()).first;
        it->second.emplace(templ);
      }
    }

    if (InductionHelper::isInductionLiteral(lit)) {
      Set<Term*,SharedTermHash>::Iterator citer1(int_terms);
      while(citer1.hasNext()){
        Term* t = citer1.next();
        auto leBound = iterTraits(_helper.getLess(t)).collect<Stack>();
        auto grBound = iterTraits(_helper.getGreater(t)).collect<Stack>();
        auto indLitsIt = contextReplacementInstance(InductionContext({ t }, lit, premise), _opt, _fnDefHandler);
        while (indLitsIt.hasNext()) {
          auto ctx = indLitsIt.next();
          // process lower bounds
          for (const auto& b1 : leBound) {
            if (!isValidBound(ctx, b1)) {
              continue;
            }
            if (_helper.isInductionForFiniteIntervalsOn()) {
              // process upper bounds together with current lower bound
              for (const auto& b2 : grBound) {
                if (!isValidBound(ctx, b2)) {
                  continue;
                }
                performFinIntInduction(ctx, b1, b2);
              }
            }
            // process current lower bound by itself
            if (_helper.isInductionForInfiniteIntervalsOn()) {
              performInfIntInduction(ctx, true, b1);
            }
          }
          // process upper bounds
          if (_helper.isInductionForInfiniteIntervalsOn()) {
            for (const auto& b2 : grBound) {
              if (!isValidBound(ctx, b2)) {
                continue;
              }
              performInfIntInduction(ctx, false, b2);
            }
          }
          // add formula with default bound
          if (_opt.integerInductionDefaultBound()) {
            InductionFormulaIndex::Entry* e = nullptr;
            static Bound defaultBound = Bound(DefaultBound{ .term = TypedTermList(theory->representConstant(IntegerConstantType(0))) });
            // for now, represent default bounds with no bound in the index, this is unique
            // since the placeholder is still int
            if (notDoneInt(ctx, nullptr, nullptr, e) && isValidBound(ctx, defaultBound)) {
              performIntInduction(ctx, e, true, defaultBound, nullptr);
              performIntInduction(ctx, e, false, defaultBound, nullptr);
            }
            resolveClauses(ctx, e, nullptr, nullptr);
          }
        }
      }
    }
    // collect term queries for each induction term
    auto sideLitsIt = VirtualIterator<pair<Stack<Term*>, VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>>>::getEmpty();
    if (_opt.nonUnitInduction()) {
      sideLitsIt = pvi(iterTraits(getSTLIterator(ta_terms.begin(), ta_terms.end()))
        .map([](const auto& kv){
          return kv.first;
        })
        .map([this](Stack<Term*> ts) {
          auto res = VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>::getEmpty();
          for (const auto& t : ts) {
            res = pvi(concatIters(res, _structInductionTermIndex->getGeneralizations(t, false)));
          }
          return make_pair(ts, res);
        }));
    }
    // put clauses from queries into contexts alongside with the given clause and induction term
    auto sideLitsIt2 = iterTraits(sideLitsIt)
      .flatMap(InductionContextFn(premise, lit))
      // generalize all contexts if needed
      .flatMap([this](const InductionContext& arg) {
        return contextReplacementInstance(arg, _opt, _fnDefHandler);
      })
      // filter out the ones without the premise, or only one literal
      .filter([&premise](const InductionContext& arg) {
        unsigned cnt = 0;
        bool hasPremise = false;
        for (const auto& kv : arg._cls) {
          if (kv.first == premise) {
            hasPremise = true;
          }
          cnt += kv.second.size();
        }
        return hasPremise && cnt > 1;
      });
    // collect contexts for single-literal induction with given clause
    auto indCtxSingle = iterTraits(getSTLIterator(ta_terms.begin(), ta_terms.end()))
      .map([&lit,&premise](const auto& arg) {
        return InductionContext(arg.first, lit, premise);
      })
      // generalize all contexts if needed
      .flatMap([this](const InductionContext& arg) {
        return contextReplacementInstance(arg, _opt, _fnDefHandler);
      });
    auto indCtxIt = concatIters(sideLitsIt2, indCtxSingle)
      // filter out the ones without an induction literal
      .filter([](const InductionContext& arg) {
        for (const auto& kv : arg._cls) {
          for (const auto& lit : kv.second) {
            if (InductionHelper::isInductionLiteral(lit)) {
              return true;
            }
          }
        }
        return false;
      });
    while (indCtxIt.hasNext()) {
      auto ctx = indCtxIt.next();
      static bool one = _opt.structInduction() == Options::StructuralInductionKind::ONE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool two = _opt.structInduction() == Options::StructuralInductionKind::TWO ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool three = _opt.structInduction() == Options::StructuralInductionKind::THREE ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      static bool rec = _opt.structInduction() == Options::StructuralInductionKind::RECURSION ||
                        _opt.structInduction() == Options::StructuralInductionKind::ALL;
      InductionFormulaIndex::Entry* e;
      // generate formulas and add them to index if not done already
      if (_formulaIndex.findOrInsert(ctx, e)) {
        if (ctx._indTerms.size() == 1) {
          TermList sort = SortHelper::getResultSort(ctx._indTerms[0]);
          TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);
          if(one){
            performInduction(ctx, ta->getInductionTemplateOne(), e);
          }
          if(two){
            performInduction(ctx, ta->getInductionTemplateTwo(), e);
          }
          if(three){
            performInduction(ctx, ta->getInductionTemplateThree(), e);
          }
        }
        if (rec) {
          for (const auto& templ : ta_terms.at(ctx._indTerms)) {
            performInduction(ctx, templ, e);
          }
        }
      }
      // resolve the formulas with the premises
      for (auto& indInst : e->getInductionInstances()) {
        resolveClauses(indInst, ctx);
      }
    }
  } else {
    if (InductionHelper::isStructInductionOn() && InductionHelper::isNonGroundInductionLiteral(lit)) {
      // TODO: generalize to multiple free variables
      NonVariableNonTypeIterator nvi(lit);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        if (InductionHelper::isInductionTerm(st) && InductionHelper::isStructInductionTerm(st)) {
          auto indLitsIt = contextReplacementInstance(InductionContext({ st }, lit, premise), _opt, _fnDefHandler);
          while (indLitsIt.hasNext()) {
            auto ctx = indLitsIt.next();
            InductionFormulaIndex::Entry* e;
            // TODO: make sure that the index handles literals with free variables correctly
            // (right now it might allow redundant induction applications due to variable renaming).
            if (_formulaIndex.findOrInsert(ctx, e)) {
              // Generate induction axioms, clausify and resolve them
              performStructInductionFreeVar(ctx, e);
            }
            for (auto& indInst : e->getInductionInstances()) {
              resolveClauses(indInst, ctx);
            }
          }
        }
      }
    }
  }
}

void InductionClauseIterator::processIntegerComparison(Clause* premise, Literal* lit)
{
  ASS((theory->interpretPredicate(lit) == Theory::INT_LESS) && lit->ground());

  bool positive = lit->isPositive();
  InductionFormulaIndex::Entry* e;
  // loop over the arguments of the comparison (i.e. the two bounds)
  for (unsigned i = 0; i <= 1; i++) {
    // i == 0 means 'bound' is upper bound,
    // i == 1 means 'bound' is lower bound
    auto indtl = *lit->nthArgument(positive ? i : 1-i);
    auto indt = indtl.term();
    auto bound = *lit->nthArgument(positive ? 1-i : i);

    auto bound2 = iterTraits(i ? _helper.getGreater(indt) : _helper.getLess(indt)).collect<Stack>();
    auto it = iterTraits(_helper.getTQRsForInductionTerm(indt))
      .filter([&premise](const auto& tqr) {
        return tqr.data->clause != premise;
      })
      .map([&indt](const auto& tqr) {
        return InductionContext({ indt }, tqr.data->literal, tqr.data->clause);
      })
      .flatMap([this](const InductionContext& arg) {
        return contextReplacementInstance(arg, _opt, _fnDefHandler);
      });
    auto b = TermLiteralClause{ TypedTermList(bound, IntTraits::sort()), lit, premise };
    // loop over literals containing the current induction term
    while (it.hasNext()) {
      auto ctx = it.next();
      if (!isValidBound(ctx, b)) {
        continue;
      }
      if (_helper.isInductionForFiniteIntervalsOn()) {
        // go over the lower/upper bounds that contain the same induction term as the current bound
        for (const auto& b2 : bound2) {
          if (!isValidBound(ctx, b2)) {
            ASS_EQ(ctx._cls.size(), 1);
            continue;
          }
          // TODO use performFinIntInduction
          if (notDoneInt(ctx, i ? lit : b2.literal, i ? b2.literal : lit, e)) {
            // TODO: this branching should be deleted, since both upward and downward can
            // be generated based on the given clause but the original code had it like this
            if (i) {
              performIntInduction(ctx, e, true, i ? b : b2, i ? &b2 : &b);
            } else {
              performIntInduction(ctx, e, false, i ? b2 : b, i ? &b : &b2);
            }
          }
          resolveClauses(ctx, e, i ? &b : &b2, i ? &b2 : &b);
        }
      }
      // use given clause comparison as bound appropriately
      if (_helper.isInductionForInfiniteIntervalsOn()) {
        performInfIntInduction(ctx, i, b);
      }
    }
  }
}

ClauseStack InductionClauseIterator::produceClauses(Formula* hypothesis, InferenceRule rule, const InductionContext& context, Substitution& cnfSubst)
{
  NewCNF cnf(0);
  cnf.setForInduction();
  ClauseStack hyp_clauses;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  unsigned maxInductionDepth = 0;
  for (const auto& kv : context._cls) {
    maxInductionDepth = max(maxInductionDepth,kv.first->inference().inductionDepth());
  }
  inf.setInductionDepth(maxInductionDepth+1);

  FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
  if(_opt.showInduction()){
    std::cout << "[Induction] formula " << fu->toString() << endl;
  }

  cnf.clausify(NNF::ennf(fu), hyp_clauses, &cnfSubst);
  return hyp_clauses;
}

// helper function to properly add bounds to integer induction contexts,
// where the bounds are not part of the inner formula for the induction
void InductionClauseIterator::resolveClauses(const InductionContext& context, InductionFormulaIndex::Entry* e, const TermLiteralClause* bound1, const TermLiteralClause* bound2)
{
  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  ASS_EQ(context._indTerms.size(), 1);
  static TypedTermList ph(getPlaceholderForTerm(context._indTerms,0));
  auto cls = context._cls;
  // lower bound
  if (bound1) {
    auto lhs = bound1->literal->polarity() ? bound1->term : ph;
    auto rhs = bound1->literal->polarity() ? ph : bound1->term;
    cls.emplace(bound1->clause,
      LiteralStack{ Literal::create2(less, bound1->literal->polarity(), lhs, rhs) });
  }
  // upper bound
  if (bound2) {
    auto lhs = bound2->literal->polarity() ? ph : bound2->term;
    auto rhs = bound2->literal->polarity() ? bound2->term : ph;
    cls.emplace(bound2->clause,
      LiteralStack{ Literal::create2(less, bound2->literal->polarity(), lhs, rhs) });
  }
  // true if we have a default bound
  InductionContext ctx(context._indTerms, std::move(cls));
  for (auto& indInst : e->getInductionInstances()) {
    resolveClauses(indInst, ctx);
  }
}

/**
 * An induction gives back a set of clauses for which it holds that:
 * - each one contains toResolve many conclusion literals
 * - for each set of literals in toResolve, there is a corresponding
 *   set of clauses that differ only in one literal pairwise, and this
 *   literal is the complement of a literal from the set of toResolve
 *   after applying subst
 * These constraints give a partitioning of clauses, where each partition
 * has a sequence of resolutions with the clauses from context, s.t.
 * only the literals not in toResolve nor in the conclusion are present
 * in the resulting clause. We find this partition and return it in form
 * of a union find structure.
 */
IntUnionFind findDistributedVariants(const InductionInstance& indInst, const InductionContext& context)
{
  const auto& toResolve = context._cls;
  IntUnionFind uf(indInst.cls.size());
  for (unsigned i = 0; i < indInst.cls.size(); i++) {
    auto cl = indInst.cls[i];
    LiteralStack conclusionLits(toResolve.size());
#if VDEBUG
    Stack<int> variantCounts(toResolve.size());
#endif
    // we first find the conclusion literals in cl, exactly 1 from
    // each of toResolve and save how many variants it should have
    for (unsigned k = 0; k < cl->length(); k++) {
      auto clit = indInst.subst.apply(Literal::complementaryLiteral((*cl)[k]), INDUCTION_CLAUSE_BANK);
      for (unsigned r_i = 0; r_i < toResolve.size(); r_i++) {
#if VDEBUG
        bool found = false;
#endif
        for (const auto& lit : toResolve[r_i].second) {
          auto slit = indInst.subst.apply(lit, NUM_SPECIAL_BANKS + r_i);
          if (slit == clit) {
            conclusionLits.push((*cl)[k]);
#if VDEBUG
            variantCounts.push(toResolve[r_i].second.size()-1);
            ASS(!found);
            found = true;
#else
            break;
#endif
          }
        }
      }
    }
    // cl should have the same number of conclusion
    // literals as the size of toResolve
    ASS_EQ(conclusionLits.size(), toResolve.size());
    // now we look for the variants
    for (unsigned k = 0; k < conclusionLits.size(); k++) {
#if VDEBUG
      for (unsigned j = 0; j < indInst.cls.size(); j++) {
#else
      for (unsigned j = i+1; j < indInst.cls.size(); j++) {
#endif
        auto other = indInst.cls[j];
        if (i == j || cl->length() != other->length()) {
          continue;
        }
        if (other->contains(conclusionLits[k])) {
          continue;
        }
        unsigned mismatchCnt = 0;
        for (unsigned l = 0; l < cl->length(); l++) {
          if (!cl->contains((*other)[l])) {
            mismatchCnt++;
          }
        }
        if (mismatchCnt == 1) {
#if VDEBUG
          variantCounts[k]--;
#endif
          uf.doUnion(i,j);
        }
      }
      ASS_LE(variantCounts[k],0);
    }
  }
  uf.evalComponents();
  return uf;
}

/**
 * Resolve a set of clauses given by findDistributedVariants with the
 * clauses from an induction context. The resulting clause can be seen
 * as the result of a sequence of resolutions and duplicate literal removals.
 */
Clause* resolveClausesHelper(const InductionContext& context, const InductionInstance& indInst, IntUnionFind::ElementIterator eIt)
{
  ASS(eIt.hasNext());
  auto cl = indInst.cls[eIt.next()];
  auto premises = UnitList::singleton(cl);
  for (const auto& index : iterTraits(eIt)) {
    UnitList::push(indInst.cls[index],premises);
  }

  // This replaces the placeholder terms with the terms we induct on in the result literals.
  TermReplacement tr(getContextReplacementMap(context, /*inverse=*/true));
  RStack<Literal*> resLits;

  // The clauses in eIt contain the same literals that will *not*
  // be resolved, so we just take the first and find these literals.
  for (const auto& curr : *cl) {
    auto clit = indInst.subst.apply(curr, INDUCTION_CLAUSE_BANK);
    bool shouldResolveLit = iterTraits(range(0, context._cls.size()))
      .any([&](unsigned i) {
        return iterTraits(context._cls[i].second.iter())
          .any([&](Literal* lit) {
            return Literal::complementaryLiteral(clit) == indInst.subst.apply(lit, NUM_SPECIAL_BANKS + i);
          });
      });
    if (!shouldResolveLit) {
      resLits->push(tr.transformLiteral(clit));
    }
  }

  // Next, we find all literals that are not resolved from clauses
  // in context._cls, and save all these clauses as premises.
  for (unsigned i = 0; i < context._cls.size(); i++) {
    const auto& [cl, lits] = context._cls[i];
    for (const auto& clit : *cl) {
      bool shouldResolveLit = iterTraits(lits.iter())
        .any([&](Literal* lit) {
          return clit == tr.transformLiteral(lit);
        });
      if (!shouldResolveLit) {
        resLits->push(tr.transformLiteral(indInst.subst.apply(clit, NUM_SPECIAL_BANKS + i)));
      }
    }
    UnitList::push(cl, premises);
  }

  return Clause::fromStack(*resLits, GeneratingInferenceMany(InferenceRule::INDUCTION_HYPERRESOLUTION, premises));
}

void InductionClauseIterator::resolveClauses(const InductionInstance& indInst, const InductionContext& context)
{
  ASS(indInst.cls.isNonEmpty());
  env.statistics->inductionApplication++;

  auto uf = findDistributedVariants(indInst, context);
  IntUnionFind::ComponentIterator cit(uf);
  while(cit.hasNext()){
    IntUnionFind::ElementIterator eIt = cit.next();
    _clauses.push(resolveClausesHelper(context, indInst, eIt));
    if(_opt.showInduction()){
      std::cout << "[Induction] generate " << _clauses.top()->toString() << endl;
    }
  }
}

void InductionClauseIterator::performFinIntInduction(const InductionContext& context, const TermLiteralClause& lb, const TermLiteralClause& ub)
{
  InductionFormulaIndex::Entry* e = nullptr;
  if (notDoneInt(context, lb.literal, ub.literal, e)) {
    performIntInduction(context, e, true, lb, &ub);
    performIntInduction(context, e, false, ub, &lb);
  }
  resolveClauses(context, e, &lb, &ub);
}

void InductionClauseIterator::performInfIntInduction(const InductionContext& context, bool increasing, const TermLiteralClause& bound)
{
  InductionFormulaIndex::Entry* e = nullptr;
  if (notDoneInt(context, increasing ? bound.literal : nullptr, increasing ? nullptr : bound.literal, e)) {
    performIntInduction(context, e, increasing, bound, nullptr);
  }
  resolveClauses(context, e, increasing ? &bound : nullptr, increasing ? nullptr : &bound);
}

std::unique_ptr<InductionTemplate> InductionClauseIterator::getIntegerInductionTemplate(bool increasing, Coproduct<TermLiteralClause, DefaultBound> bound1, const TermLiteralClause* optionalBound2)
{
  TermList b1(bound1.apply([](auto x) { return x.term; }));

  auto x = TermList::var(0);
  auto y = TermList::var(1);

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  LiteralStack stepConds = {
    Literal::create2(less,false,(increasing ? x : b1),(increasing ? b1 : x))
  };

  // create Y>=b1 (which is ~Y<b1), or Y>b1, or Y<=b1 (which is ~b1<Y), or Y<b1
  // This comparison is mirroring the structure of bound1.literal, which is "b1 <comparison> inductionTerm".
  // If bound1.literal is nullptr, we are using the default bound with the comparison sign >= or <=.
  const bool isBound1Equal = bound1.match(
      [](TermLiteralClause const& bound1) { return (bound1.literal->functor() == less && bound1.literal->isNegative()); },
      [](DefaultBound) { return true; });
  const bool isBound1FirstArg = (increasing != isBound1Equal);
  LiteralStack concConds = {
    Literal::create2(less, !isBound1Equal, (isBound1FirstArg ? b1 : y), (isBound1FirstArg ? y : b1))
  };

  const bool hasBound2 = optionalBound2 && optionalBound2->literal;
  // Also resolve the hypothesis with comparisons with bound(s) (if the bound(s) are present/not default).
  if (hasBound2) {
    // Finite interval induction, use two bounds on both x and y.
    TermList b2(optionalBound2->term);
    if (b1 == b2) {
      return std::unique_ptr<InductionTemplate>();
    }
    // create X<b2 or X>b2 (which is b2<X)
    stepConds.push(Literal::create2(less, true, (increasing ? x : b2), (increasing ? b2 : x)));
    const bool isBound2Equal = (optionalBound2->literal->functor() == less && optionalBound2->literal->isNegative());
    const bool isBound2FirstArg = (increasing == isBound2Equal);
    // create Y<b2, or Y<=b2 (which is ~b2<Y) or Y>b2, or Y>=b2 (which is ~Y<b2)
    concConds.push(Literal::create2(less, !isBound2Equal, (isBound2FirstArg ? b2 : y), (isBound2FirstArg ? y : b2)));
  }

  TermList xPlusOne(Term::create2(
    env.signature->getInterpretingSymbol(Theory::INT_PLUS), x,
    TermList(theory->representConstant(IntegerConstantType(increasing ? 1 : -1))))
  );
  Stack<InductionCase> cases {
    InductionCase(InductionUnit({ b1 })), // base case
    InductionCase(InductionUnit({ xPlusOne }, std::move(stepConds)), { TermStack{ x } }) // step case
  };

  const bool isDefaultBound = bound1.template is<DefaultBound>();
  InferenceRule rule =
      isDefaultBound
          ? (increasing ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
          : (increasing ? (hasBound2 ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM : InferenceRule::INT_INF_UP_INDUCTION_AXIOM)
                        : (hasBound2 ? InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));

  return make_unique<InductionTemplate>(
    TermStack{ AtomicSort::intSort() },
    std::move(cases),
    InductionUnit({ y }, std::move(concConds)),
    /*maxVar=*/y.var(), rule
  );
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
void InductionClauseIterator::performIntInduction(const InductionContext& context, InductionFormulaIndex::Entry* e, bool increasing, Coproduct<TermLiteralClause, DefaultBound> bound1, const TermLiteralClause* optionalBound2)
{
  auto templ = getIntegerInductionTemplate(increasing, bound1, optionalBound2);
  if (!templ) {
    return;
  }
  performInduction(context, templ.get(), e);
}

void InductionClauseIterator::performInduction(const InductionContext& context, const InductionTemplate* templ, InductionFormulaIndex::Entry* e)
{
  unsigned var = templ->maxVar+1;
  auto formulas = FormulaList::empty();
  std::vector<TermList> ts(context._indTerms.size(), TermList());

  static Substitution typeBinder;
  typeBinder.reset();

  ASS_EQ(context._indTerms.size(), templ->sorts.size());
  for (unsigned i = 0; i < context._indTerms.size(); i++) {
    ALWAYS(MatchingUtils::matchTerms(templ->sorts[i], SortHelper::getResultSort(context._indTerms[i]), typeBinder));
  }

  for (const auto& c : templ->cases) {
    auto hyps = FormulaList::empty();
    for (const auto& hyp : c.hypotheses) {
      auto varsReplacingSkolems = VList::empty();
      auto hypF = context.getFormula(hyp, typeBinder, var, &varsReplacingSkolems);
      // The variables replacing Skolems are used in a similar manner to strengthen
      // hypotheses as condUnivVars in InductionUnit and hypUnivVars in InductionCase,
      // but they are different for each hypothesis, so we quantify them here.
      if (varsReplacingSkolems) {
        hypF = new QuantifiedFormula(Connective::FORALL, varsReplacingSkolems, SList::empty(), hypF);
      }
      FormulaList::push(hypF, hyps);
    }
    auto left = hyps ? JunctionFormula::generalJunction(Connective::AND, hyps) : nullptr;
    auto hypVars = VList::fromIterator(c.hypUnivVars.iterFifo());
    if (hypVars) {
      ASS(left);
      left = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), left);
    }
    auto right = context.getFormula(c.conclusion, typeBinder, var);
    FormulaList::push(Formula::quantify(left ? new BinaryFormula(Connective::IMP,left,right) : right), formulas);
  }
  ASS(formulas);
  auto indPremise = JunctionFormula::generalJunction(Connective::AND,formulas);

  RobSubstitution subst;
  auto conclusion = context.getFormula(templ->conclusion, typeBinder, var, nullptr, &subst);
  Formula* induction_formula = new BinaryFormula(Connective::IMP, indPremise, Formula::quantify(conclusion));

  // Produce induction clauses and obtain the skolemization bindings.
  Substitution cnfSubst;
  auto cls = produceClauses(induction_formula, templ->rule, context, cnfSubst);
  for (const auto& [v,t] : iterTraits(cnfSubst.items())) {
    ALWAYS(subst.unify(TermList::var(v),INDUCTION_CLAUSE_BANK,t,INDUCTION_CLAUSE_BANK));
  }
  e->add(std::move(cls), std::move(subst));
}

/*
Creates the structural induction axiom with an existentially quantified variable:
?y,w. !u0,us,z. ?x. (L[0, u0] & (L[y, w] -> L[s(y), us]) -> L[z, x])
*/
void InductionClauseIterator::performStructInductionFreeVar(const InductionContext& context, InductionFormulaIndex::Entry* e)
{
  ASS_EQ(context._indTerms.size(), 1);

  TermList sort = SortHelper::getResultSort(context._indTerms[0]);
  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);

  // Synthesis specific:
  SynthesisALManager* synthMan = static_cast<SynthesisALManager*>((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) ? SynthesisALManager::getInstance() : nullptr);
  std::vector<Term*> fnHeads;
  vector<Shell::SkolemTracker> skolemTrackers;

  unsigned numTypeArgs = sort.term()->arity();
  unsigned freeVar = context.getFreeVariable(); // variable free in the induction literal
  unsigned var = freeVar + 1 + (synthMan ? synthMan->numInputSkolems() : 0); // used in the following to construct new variables
  for (const auto& kv : context._cls) {
    if (kv.first->maxVar() + 1 > var) {
      var = kv.first->maxVar() + 1;
    }
  }
  VList* us = VList::empty();
  VList* ws = VList::empty();
  VList* ys = VList::empty();
  FormulaList* formulas = FormulaList::empty();

  // Construct premise as a conjunction of steps.
  // Each step's antecedent contains a fresh free variable in place
  // of freeVar (collected in `ws`), each step's conclusion too (collected in `us`).
  for (unsigned i = 0; i < ta->nConstructors(); i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
    TermStack argTerms(arity); // Arguments of the step case antecedent: y_1, ..., y_arity
    argTerms.loadFromIterator(Term::Iterator(sort.term()));
    FormulaList* hyps = FormulaList::empty();
    for (unsigned j = numTypeArgs; j < arity; j++){
      TermList y(var++, false);
      argTerms.push(y);
      VList::push(y.var(), ys);
      if (con->argSort(j) == con->rangeSort()){
        unsigned w = var++;
        VList::push(w, ws);
        Formula* curLit = context.getFormulaWithFreeVar(y, freeVar, w);
        FormulaList::push(curLit, hyps); // L[y_j, w_j]
        // Synthesis specific:
        if (synthMan) {
          // Store SkolemTrackers before skolemization happens. Later (after skolemization), they will be used to match Skolem symbols.
          skolemTrackers.emplace_back(Binding(w, nullptr), i, true, j);
        }
      }
      // Synthesis specific:
      if (synthMan) {
        // Store SkolemTrackers before skolemization happens. Later (after skolemization), they will be used to match Skolem symbols.
        skolemTrackers.emplace_back(Binding(y.var(), nullptr), i, false, j);
      }
    }
    unsigned u = var++;
    VList::push(u, us);

    Term* tcons = Term::create(con->functor(), (unsigned)argTerms.size(), argTerms.begin());

    // Synthesis specific:
    if (synthMan) {
      fnHeads.push_back(tcons);
    }

    Formula* consequent = context.getFormulaWithFreeVar({ TermList(tcons) }, freeVar, u);
    Formula* step = (VList::isEmpty(ws)) ? consequent :
      new BinaryFormula(Connective::IMP, JunctionFormula::generalJunction(Connective::AND, hyps), consequent); // (/\_{j ∈ P_c} L[y_j, w_j]) --> L[cons(y_1, ..., y_n), u_i]
    formulas->push(step, formulas);
  }
  Formula* formula = new JunctionFormula(Connective::AND, formulas);

  // Construct conclusion: L[z, x]
  TermList z(var++, false);
  unsigned x = var++;
  RobSubstitution subst;
  Formula* conclusion = context.getFormulaWithFreeVar(z, freeVar, x, &subst);
  // Put together the whole induction axiom:
  formula = new BinaryFormula(Connective::IMP, formula, conclusion);
  formula = new QuantifiedFormula(Connective::EXISTS, VList::singleton(x), SList::empty(), formula);
  formula = new QuantifiedFormula(Connective::FORALL, VList::singleton(z.var()), SList::empty(), formula);
  formula = new QuantifiedFormula(Connective::FORALL, us, SList::empty(), formula);
  if (!VList::isEmpty(ws)) {
    formula = new QuantifiedFormula(Connective::EXISTS, ws, SList::empty(), formula);
  }
  if (!VList::isEmpty(ys)) {
    formula = new QuantifiedFormula(Connective::EXISTS, ys, SList::empty(), formula);
  }

  // Produce induction clauses and obtain the skolemization bindings.
  Substitution cnfSubst;
  ClauseStack hyp_clauses = produceClauses(formula, InferenceRule::STRUCT_INDUCTION_AXIOM_ONE, context, cnfSubst);
  // Bind freeVar to its corresponding skolem term in freeVarSubst.
  // This is used later in resolution.
  TermList xSkolem(cnfSubst.apply(x));
  ASS(xSkolem.isTerm());
  ASS_EQ(*(xSkolem.term()->nthArgument(xSkolem.term()->arity()-1)), z);
  ALWAYS(subst.unify(TermList::var(freeVar),NUM_SPECIAL_BANKS,xSkolem,INDUCTION_CLAUSE_BANK));

  // Synthesis specific:
  if (synthMan) {
    synthMan->registerSkolemSymbols(xSkolem.term(), cnfSubst, fnHeads, skolemTrackers, us);
  }

  e->add(std::move(hyp_clauses), std::move(subst));
}

bool InductionClauseIterator::notDoneInt(InductionContext context, Literal* bound1, Literal* bound2, InductionFormulaIndex::Entry*& e)
{
  ASS_EQ(context._indTerms.size(), 1);
  TermList ph(getPlaceholderForTerm(context._indTerms,0));
  Literal* b1 = nullptr;
  Literal* b2 = nullptr;
  if (bound1) {
    b1 = Literal::create2(bound1->functor(), bound1->polarity(),
      bound1->polarity() ? *bound1->nthArgument(0) : ph,
      bound1->polarity() ? ph : *bound1->nthArgument(1));
  }
  if (bound2) {
    b2 = Literal::create2(bound2->functor(), bound2->polarity(),
      bound2->polarity() ? ph : *bound2->nthArgument(0),
      bound2->polarity() ? *bound2->nthArgument(1) : ph);
  }
  return _formulaIndex.findOrInsert(context, e, b1, b2);
}

bool InductionClauseIterator::isValidBound(const InductionContext& context, const Bound& bound)
{
  ASS_EQ(context._indTerms.size(), 1);
  Term* pt = getPlaceholderForTerm(context._indTerms,0);
  for (const auto& kv : context._cls) {
    for (const auto& lit : kv.second) {
      ASS((lit != nullptr) && (kv.first != nullptr));
      Term* otherArg = InductionHelper::getOtherTermFromComparison(lit, pt);
      if (!bound.match(
            [&](TermLiteralClause const&  bound)
            { return InductionHelper::isValidBound(otherArg, kv.first, bound); },
            [&](DefaultBound const& bound)
            { return InductionHelper::isValidForDefaultBound(otherArg, kv.first, bound.term); }
            )) {
        return false;
      }
    }
  }
  return true;
}

}
