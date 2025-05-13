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
#include <set>

#include "Lib/Output.hpp"
#include "Forwards.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"

#include "Indexing/ResultSubstitution.hpp"
#include "Lib/BitUtils.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Set.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"
#include "Kernel/NumTraits.hpp"

#include "Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{
using namespace std;
using namespace Kernel;
using namespace Lib; 

bool ActiveOccurrenceIterator::hasNext() {
  while (_returnStack.isEmpty() && !_processStack.isEmpty()) {
    Term* t = _processStack.pop();
    if (t->ground()) {
      _returnStack.push(t);
    }
    auto templ = _fnDefHandler.getRecursionTemplate(t);
    auto actPos = templ ? &templ->inductionPositions() : nullptr;
    for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
      if ((!actPos || (*actPos)[i]) && t->nthArgument(i)->isTerm()) {
        _processStack.push(t->nthArgument(i)->term());
      }
    }
  }
  return !_returnStack.isEmpty();
}

Term* ActiveOccurrenceIterator::next()
{
  return _returnStack.pop();
}

Term* getPlaceholderForTerm(const std::vector<Term*>& ts, unsigned i)
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

TermList SkolemSquashingTermReplacement::transformSubterm(TermList trm)
{
  if (trm.isVar() || trm.term()->isSort()) {
    return trm;
  }
  auto t = trm.term();
  auto it = _m.find(t);
  if (it != _m.end()){
    return it->second;
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
  return trm;
}

Formula* InductionContext::getFormula(const InductionUnit& unit, const TypeBinder& typeBinder, unsigned& var, VList** varList, Substitution* subst) const
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
  auto right = getFormulaWithSquashedSkolems(ts, var, varList, subst);
  return left ? new BinaryFormula(Connective::IMP, left, right) : right;
};

Formula* InductionContext::getFormula(TermReplacement& tr) const
{
  ASS(!_cls.empty());
  auto argLists = FormulaList::empty();
  for (const auto& kv : _cls) {
    auto argList = FormulaList::empty();
    for (const auto& lit : kv.second) {
      auto tlit = tr.transformLiteral(lit);
      FormulaList::push(new AtomicFormula(Literal::complementaryLiteral(tlit)), argList);
    }
    FormulaList::push(JunctionFormula::generalJunction(Connective::AND, argList), argLists);
  }
  return JunctionFormula::generalJunction(Connective::OR, argLists);
}

Formula* InductionContext::getFormula(const std::vector<TermList>& r, Substitution* subst) const
{
  ASS_EQ(_indTerms.size(), r.size());

  // Assuming this object is the result of a ContextReplacement (or similar iterator)
  // we can replace the ith placeholder with the ith term in r.
  std::map<Term*,TermList> replacementMap;
  for (unsigned i = 0; i < _indTerms.size(); i++) {
    auto ph = getPlaceholderForTerm(_indTerms,i);
    replacementMap.insert(make_pair(ph,r[i]));
    if (subst) {
      ASS(r[i].isVar());
      subst->bind(r[i].var(), ph);
    }
  }
  TermReplacement tr(replacementMap);
  return getFormula(tr);
}

Formula* InductionContext::getFormulaWithFreeVar(const std::vector<TermList>& r, unsigned freeVar, TermList& freeVarSub, Substitution* subst) const
{
  Formula* replaced = getFormula(r, subst);
  Substitution s;
  s.bind(freeVar, freeVarSub);
  return SubstHelper::apply(replaced, s);
}

Formula* InductionContext::getFormulaWithSquashedSkolems(const std::vector<TermList>& r,
  unsigned& var, VList** varList, Substitution* subst) const
{
  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return getFormula(r, subst);
  }
  std::map<Term*,TermList> replacementMap;
  for (unsigned i = 0; i < _indTerms.size(); i++) {
    auto ph = getPlaceholderForTerm(_indTerms,i);
    replacementMap.insert(make_pair(ph,r[i]));
    if (subst) {
      ASS(r[i].isVar());
      subst->bind(r[i].var(), ph);
    }
  }
  SkolemSquashingTermReplacement tr(replacementMap, var);
  unsigned temp = var;
  auto res = getFormula(tr);
  if (subst) {
    DHMap<Term*,unsigned,SharedTermHash>::Iterator it(tr._tv);
    while (it.hasNext()) {
      unsigned v;
      Term* t;
      it.next(t, v);
      subst->bind(v,t);
    }
  }
  if (varList) {
    // The variables replacing the Skolems after calling transform
    // are needed for quantification if varList is non-null, collect them
    for (unsigned i = temp; i < var; i++) {
      VList::push(i,*varList);
    }
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
  ASSERTION_VIOLATION_REP("Called getFreeVariable on InductionContext without free variables");
  return 0;
}

std::map<Term*,TermList> getContextReplacementMap(const InductionContext& context, bool inverse = false)
{
  std::map<Term*,TermList> m;
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
  InductionContext context(_context._indTerms);
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = transformLiteral(lit);
      if (tlit != lit) {
        context.insert(kv.first, tlit);
      }
    }
  }
  _used = true;
  return context;
}

ActiveOccurrenceContextReplacement::ActiveOccurrenceContextReplacement(
  const InductionContext& context, FunctionDefinitionHandler& fnDefHandler)
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
  InductionContext context(_context._indTerms);
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      for (unsigned i = 0; i < _iteration.size(); i++) {
        _iteration[i] = 0;
        _matchCount[i] = 0;
      }
      Stack<pair<Term*,bool>> stack(8);
      stack.push(make_pair(lit,true));
      while (stack.isNonEmpty()) {
        auto kv = stack.pop();
        auto t = kv.first;
        auto active = kv.second;
        auto templ = _fnDefHandler.getRecursionTemplate(t);
        for (unsigned k = 0; k < t->arity(); k++) {
          if (t->nthArgument(k)->isTerm()) {
            stack.push(make_pair(t->nthArgument(k)->term(),
              active && templ ? templ->inductionPositions()[k] : active));
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
      auto tlit = transformLiteral(lit);
      if (tlit != lit) {
        context.insert(kv.first, tlit);
      }
    }
  }
  // TODO enforce this
  // ASS(!context._cls.empty());
  return context;
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
    if (!ao_ctx._cls.empty()) {
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
  InductionContext context(_context._indTerms);
  for (unsigned i = 0; i < _context._indTerms.size(); i++) {
    _matchCount[i] = 0;
  }
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = transformLiteral(lit);
      // check if tlit has placeholders
      bool found = false;
      for (unsigned i = 0; i < _context._indTerms.size(); i++) {
        if (tlit->containsSubterm(TermList(getPlaceholderForTerm(_context._indTerms,i)))) {
          found = true;
          break;
        }
      }
      if (found) {
        context.insert(kv.first, tlit);
      }
    }
  }
  _ready = false;
  return context;
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
  if (InductionHelper::isIntInductionOneOn()) {
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
  if (InductionHelper::isIntInductionOneOn()) {
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
    for (unsigned i=0;i<premise->length();i++) {
      processLiteral(premise,(*premise)[i]);
    }
  }
  if (InductionHelper::isIntInductionOneOn() && InductionHelper::isIntegerComparison(premise)) {
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

  VirtualIterator<InductionContext> operator()(pair<std::vector<Term*>, VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>> arg) {
    auto indDepth = _premise->inference().inductionDepth();
    // heuristic 2
    if (indDepth) {
      auto res = VirtualIterator<InductionContext>::getEmpty();
      // TODO make this work for multiple induction terms
      ASS(arg.first.size() >= 1)
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
        InductionContext ctx(arg.first, _lit, _premise);
        ctx.insert(tqr.clause, tqr.literal);
        res = pvi(concatIters(res, getSingletonIterator(ctx)));
      }
      return res;
    // heuristic 1
    } else {
      InductionContext ctx(arg.first, _lit, _premise);
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
        ctx.insert(tqr.clause, tqr.literal);
      }
      return pvi(getSingletonIterator(ctx));
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

  if (lit->ground()) {
      Set<Term*,SharedTermHash> int_terms;
      typedef std::set<const InductionTemplate*> TemplateTypeArgsSet;
      std::map<std::vector<Term*>,TemplateTypeArgsSet> ta_terms;

      std::vector<Term*> indTerms;
      auto templ = _fnDefHandler.matchesTerm(lit, indTerms);
      if (templ) {
        auto it = ta_terms.emplace(std::move(indTerms), TemplateTypeArgsSet()).first;
        it->second.emplace(templ);
      }

      VirtualIterator<Term*> it;
      if (_opt.inductionOnActiveOccurrences()) {
        it = vi(new ActiveOccurrenceIterator(lit, _fnDefHandler));
      } else {
        it = vi(new NonVariableNonTypeIterator(lit));
      }
      while(it.hasNext()){
        Term* t = it.next();
        if (t->isLiteral()) {
          continue;
        }
        auto f = t->functor();
        if(InductionHelper::isInductionTermFunctor(f)){
          if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionTerm(t)){
            ta_terms.emplace(std::vector<Term*>{ t }, TemplateTypeArgsSet());
          }
          if(InductionHelper::isIntInductionOneOn() && InductionHelper::isIntInductionTermListInLiteral(t, lit)){
            int_terms.insert(t);
          }
        }
        std::vector<Term*> indTerms;
        auto templ = _fnDefHandler.matchesTerm(t, indTerms);
        if (templ) {
          auto it = ta_terms.emplace(std::move(indTerms), TemplateTypeArgsSet()).first;
          it->second.emplace(templ);
        }
      }

    if (InductionHelper::isGroundInductionLiteral(lit)) {
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
    auto sideLitsIt = VirtualIterator<pair<std::vector<Term*>, VirtualIterator<QueryRes<ResultSubstitutionSP, TermLiteralClause>>>>::getEmpty();
    if (_opt.nonUnitInduction()) {
      sideLitsIt = pvi(iterTraits(getSTLIterator(ta_terms.begin(), ta_terms.end()))
        .map([](const auto& kv){
          return kv.first;
        })
        .map([this](std::vector<Term*> ts) {
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
            if (InductionHelper::isGroundInductionLiteral(lit)) {
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
      for (auto& kv : e->get()) {
        resolveClauses(kv.first, ctx, kv.second);
      }
    }
  } else if (!env.options->inductionGroundOnly() && InductionHelper::isStructInductionOn() && InductionHelper::isNonGroundInductionLiteral(lit)) {
    // TODO: generalize to multiple free variables
    NonVariableNonTypeIterator nvi(lit);
    while (nvi.hasNext()) {
      auto st = nvi.next();
      if (InductionHelper::isInductionTermFunctor(st->functor()) && st->ground() && InductionHelper::isStructInductionTerm(st)) {
        auto indLitsIt = contextReplacementInstance(InductionContext({ st }, lit, premise), _opt, _fnDefHandler);
        while (indLitsIt.hasNext()) {
          auto ctx = indLitsIt.next();
          InductionFormulaIndex::Entry* e;
          // TODO: make sure that the index handles literals with free variables correctly
          // (right now it might allow redundant induction applications due to variable renaming).
          if (_formulaIndex.findOrInsert(ctx, e)) {
            // Generate induction axioms, clausify and resolve them
            Substitution freeVarSubst;
            performStructInductionFreeVar(ctx, e, &freeVarSubst);
            for (auto& kv : e->get()) {
              resolveClauses(kv.first, ctx, kv.second, /*applySubst=*/ false, &freeVarSubst);
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

ClauseStack InductionClauseIterator::produceClauses(Formula* hypothesis, InferenceRule rule, const InductionContext& context, DHMap<unsigned, Term*>* bindings)
{
  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
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
  cnf.clausify(NNF::ennf(fu), hyp_clauses, bindings);

  switch (rule) {
    case InferenceRule::STRUCT_INDUCTION_AXIOM_ONE:
    case InferenceRule::STRUCT_INDUCTION_AXIOM_TWO:
    case InferenceRule::STRUCT_INDUCTION_AXIOM_THREE:
    case InferenceRule::STRUCT_INDUCTION_AXIOM_RECURSION:
      env.statistics->structInduction++;
      break;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
      env.statistics->intInfInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
      env.statistics->intFinInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      env.statistics->intDBInduction++;
      break;
    default:
      ;
  }
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
      env.statistics->intInfUpInduction++;
      break;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
      env.statistics->intInfDownInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
      env.statistics->intFinUpInduction++;
      break;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
      env.statistics->intFinDownInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      env.statistics->intDBUpInduction++;
      break;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      env.statistics->intDBDownInduction++;
      break;
    default:
      ;
  }

  return hyp_clauses;
}

// helper function to properly add bounds to integer induction contexts,
// where the bounds are not part of the inner formula for the induction
void InductionClauseIterator::resolveClauses(InductionContext context, InductionFormulaIndex::Entry* e, const TermLiteralClause* bound1, const TermLiteralClause* bound2)
{
  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  ASS_EQ(context._indTerms.size(), 1);
  static TypedTermList ph(getPlaceholderForTerm(context._indTerms,0));
  // lower bound
  if (bound1) {
    auto lhs = bound1->literal->polarity() ? bound1->term : ph;
    auto rhs = bound1->literal->polarity() ? ph : bound1->term;
    context.insert(bound1->clause,
      Literal::create2(less, bound1->literal->polarity(), lhs, rhs));
  }
  // upper bound
  if (bound2) {
    auto lhs = bound2->literal->polarity() ? ph : bound2->term;
    auto rhs = bound2->literal->polarity() ? bound2->term : ph;
    context.insert(bound2->clause,
      Literal::create2(less, bound2->literal->polarity(), lhs, rhs));
  }
  // true if we have a default bound
  bool applySubst = !bound1 && !bound2;
  for (auto& kv : e->get()) {
    resolveClauses(kv.first, context, kv.second, applySubst);
  }
}

/**
 * An induction gives back a set of clauses for which it holds that:
 * - each one contains toResolve many conclusion literals
 * - for each set of literals in toResolve, there is a corresponding
 *   set of clauses that differ only in one literal pairwise, and this
 *   literal is the complement of a literal from the set of toResolve
 *   after applying subst
 * These contraints give a partitioning of clauses, where each partition
 * has a sequence of resolutions with the clauses from context, s.t.
 * only the literals not in toResolve nor in the conclusion are present
 * in the resulting clause. We find this partition and return it in form
 * of a union find structure.
 */
IntUnionFind findDistributedVariants(const Stack<Clause*>& clauses, Substitution& subst, const InductionContext& context, Substitution* indLitSubst)
{
  const auto& toResolve = context._cls;
  IntUnionFind uf(clauses.size());
  for (unsigned i = 0; i < clauses.size(); i++) {
    auto cl = clauses[i];
    Stack<Literal*> conclusionLits(toResolve.size());
#if VDEBUG
    Stack<int> variantCounts(toResolve.size());
#endif
    // we first find the conclusion literals in cl, exactly 1 from
    // each of toResolve and save how many variants it should have
    for (unsigned k = 0; k < cl->length(); k++) {
      auto clit = SubstHelper::apply<Substitution>(Literal::complementaryLiteral((*cl)[k]), subst);
      for (const auto& kv : toResolve) {
#if VDEBUG
        bool found = false;
#endif
        for (const auto& lit : kv.second) {
          Literal* slit = indLitSubst ? SubstHelper::apply<Substitution>(lit, *indLitSubst) : lit;
          if (slit == clit) {
            conclusionLits.push((*cl)[k]);
#if VDEBUG
            variantCounts.push(kv.second.size()-1);
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
      for (unsigned j = 0; j < clauses.size(); j++) {
#else
      for (unsigned j = i+1; j < clauses.size(); j++) {
#endif
        auto other = clauses[j];
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
 * @param rsubst is for compatibility with default bound integer induction,
 *               it is stored separately so that we don't have to apply
 *               substitutions expensively in all cases.
 */
Clause* resolveClausesHelper(const InductionContext& context, const Stack<Clause*>& cls, IntUnionFind::ElementIterator eIt, Substitution& subst, bool generalized, bool applySubst, Substitution* indLitSubst)
{
  // first create the clause with the required size
  RobSubstitution renaming;
  ASS(eIt.hasNext());
  auto cl = cls[eIt.next()];
  auto premises = UnitList::singleton(cl);
  const auto& toResolve = context._cls;
  while (eIt.hasNext()) {
    auto other = cls[eIt.next()];
    UnitList::push(other,premises);
  }

  for (const auto& kv : toResolve) {
    UnitList::push(kv.first, premises);
  }

  Inference inf(GeneratingInferenceMany(
    generalized ? InferenceRule::GEN_INDUCTION_HYPERRESOLUTION
                : ( indLitSubst ? InferenceRule::FREE_VAR_INDUCTION_HYPERRESOLUTION : InferenceRule::INDUCTION_HYPERRESOLUTION),
    premises));
  RStack<Literal*> resLits;

  for (Literal* curr : cl->iterLits()) {
    auto clit = SubstHelper::apply<Substitution>(Literal::complementaryLiteral(curr), subst);
    bool contains = false;
    for (const auto& kv : toResolve) {
      for (const auto& lit : kv.second) {
        Literal* slit = indLitSubst ? SubstHelper::apply<Substitution>(lit, *indLitSubst) : lit;
        if (slit == clit) {
          contains = true;
          break;
        }
      }
      if (contains) {
        break;
      }
    }
    if (!contains) {
      Literal* resLit;
      if (applySubst) {
        TermReplacement tr(getContextReplacementMap(context, /*inverse=*/true));
        resLit = tr.transformLiteral(SubstHelper::apply<Substitution>(curr,subst));
      } else {
        resLit = curr;
      }
      resLits->push(renaming.apply(resLit,0));
    }
  }

  for (const auto& kv : toResolve) {
    for (unsigned i = 0; i < kv.first->length(); i++) {
      bool copyCurr = true;
      for (const auto& lit : kv.second) {
        TermReplacement tr(getContextReplacementMap(context, /*inverse=*/true));
        auto rlit = tr.transformLiteral(lit);
        if (rlit == (*kv.first)[i]) {
          copyCurr = false;
          break;
        }
      }
      if (copyCurr) {
        Literal* l = (*kv.first)[i];
        if (indLitSubst) {
          l = SubstHelper::apply<Substitution>((*kv.first)[i], *indLitSubst);
          TermReplacement tr(getContextReplacementMap(context, /*inverse=*/true));
          l = tr.transformLiteral(l);
        }
        resLits->push(renaming.apply(l,1));
      }
    }
  }

  return Clause::fromStack(*resLits, inf);
}

void InductionClauseIterator::resolveClauses(const ClauseStack& cls, const InductionContext& context, Substitution& subst, bool applySubst, Substitution* indLitSubst)
{
  ASS(cls.isNonEmpty());
  bool generalized = false;
  for (const auto& kv : context._cls) {
    for (const auto& lit : kv.second) {
      for (const auto& t : context._indTerms) {
        if (lit->containsSubterm(TermList(t))) {
          generalized = true;
          break;
        }
      }
      if (generalized) {
        break;
      }
    }
    if (generalized) {
      break;
    }
  }
  if (generalized) {
    env.statistics->generalizedInductionApplication++;
  } else if (indLitSubst) {
    env.statistics->nonGroundInductionApplication++;
  } else {
    env.statistics->inductionApplication++;
  }

  auto uf = findDistributedVariants(cls, subst, context, indLitSubst);
  IntUnionFind::ComponentIterator cit(uf);
  while(cit.hasNext()){
    IntUnionFind::ElementIterator eIt = cit.next();
    _clauses.push(resolveClausesHelper(context, cls, eIt, subst, generalized, applySubst, indLitSubst));
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
  FormulaList* formulas = FormulaList::empty();
  std::vector<TermList> ts(context._indTerms.size(), TermList());

  // cout << "using template" << endl;
  // cout << *templ << endl;

  static TypeBinder typeBinder;
  typeBinder.reset();

  ASS_EQ(context._indTerms.size(), templ->sorts.size());
  for (unsigned i = 0; i < context._indTerms.size(); i++) {
    ALWAYS(MatchingUtils::matchTerms(templ->sorts[i], SortHelper::getResultSort(context._indTerms[i]), typeBinder));
  }

  for (const auto& c : templ->cases) {
    FormulaList* hyps = FormulaList::empty();
    for (const auto& hyp : c.hypotheses) {
      auto hypVars = VList::empty();
      auto hypF = context.getFormula(hyp, typeBinder, var, &hypVars);
      // quantify each hypotheses with variables replacing Skolems explicitly
      if (hypVars) {
        hypF = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), hypF);
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

  Substitution subst;
  auto conclusion = context.getFormula(templ->conclusion, typeBinder, var, nullptr, &subst);
  Formula* induction_formula = new BinaryFormula(Connective::IMP, indPremise, Formula::quantify(conclusion));
  // cout << *induction_formula << endl;

  auto cls = produceClauses(induction_formula, templ->rule, context);
  e->add(std::move(cls), std::move(subst));
}

/*
Creates the structural induction axiom with an existentially quantified variable:
?y,w. !u0,us,z. ?x. (L[0, u0] & (L[y, w] -> L[s(y), us]) -> L[z, x])
*/
void InductionClauseIterator::performStructInductionFreeVar(const InductionContext& context, InductionFormulaIndex::Entry* e, Substitution* freeVarSubst)
{
  if (context._indTerms.size() > 1) return;
  TermList sort = SortHelper::getResultSort(context._indTerms[0]);
  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(sort);
  unsigned numTypeArgs = sort.term()->arity();
  unsigned freeVar = context.getFreeVariable(); // variable free in the induction literal
  unsigned var = freeVar+1; // used in the following to construct new variables
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
        TermList w(var++, false);
        VList::push(w.var(), ws);
        Formula* curLit = context.getFormulaWithFreeVar({ y }, freeVar, w);
        FormulaList::push(curLit, hyps); // L[y_j, w_j]
      }
    }
    TermList u(var++, false);
    VList::push(u.var(), us);
    Term* tcons = Term::create(con->functor(), (unsigned)argTerms.size(), argTerms.begin());
    Formula* consequent = context.getFormulaWithFreeVar({ TermList(tcons) }, freeVar, u);
    Formula* step = (VList::isEmpty(ws)) ? consequent :
      new BinaryFormula(Connective::IMP, JunctionFormula::generalJunction(Connective::AND, hyps), consequent); // (/\_{j ∈ P_c} L[y_j, w_j]) --> L[cons(y_1, ..., y_n), u_i]
    formulas->push(step, formulas);
  }
  Formula* formula = new JunctionFormula(Connective::AND, formulas);

  // Construct conclusion: L[z, x]
  TermList z(var++, false);
  const unsigned xvar = var;
  TermList x(var++, false);
  Substitution subst;
  Formula* conclusion = context.getFormulaWithFreeVar({ z }, freeVar, x, &subst);
  // Put together the whole induction axiom:
  formula = new BinaryFormula(Connective::IMP, formula, conclusion);
  formula = new QuantifiedFormula(Connective::EXISTS, VList::singleton(xvar), SList::empty(), formula);
  formula = new QuantifiedFormula(Connective::FORALL, VList::singleton(z.var()), SList::empty(), formula);
  formula = new QuantifiedFormula(Connective::FORALL, us, SList::empty(), formula);
  if (!VList::isEmpty(ws)) {
    formula = new QuantifiedFormula(Connective::EXISTS, ws, SList::empty(), formula);
  }
  if (!VList::isEmpty(ys)) {
    formula = new QuantifiedFormula(Connective::EXISTS, ys, SList::empty(), formula);
  }

  // Produce induction clauses and obtain the skolemization bindings.
  DHMap<unsigned, Term*> bindings;
  ClauseStack hyp_clauses = produceClauses(formula, InferenceRule::STRUCT_INDUCTION_AXIOM_ONE, context, &bindings); 
  // Bind freeVar to its corresponding skolem term in freeVarSubst.
  // This is used later in resolution.
  Term* xSkolem = bindings.get(xvar, nullptr);
  ASS(xSkolem != nullptr);
  ASS(freeVarSubst != nullptr);
  freeVarSubst->bind(int(freeVar), SubstHelper::apply<Substitution>(xSkolem, subst));

  e->add(std::move(hyp_clauses), std::move(subst));
  return;
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
