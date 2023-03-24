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

#include "Forwards.hpp"
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

#include "Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 

Term* getPlaceholderForTerm(Term* t)
{
  CALL("getPlaceholderForTerm");
  static DHMap<TermList,Term*> placeholders;
  TermList srt = env.signature->getFunction(t->functor())->fnType()->result();
  if(!placeholders.find(srt)){
    unsigned fresh = env.signature->addFreshFunction(0,(srt.toString() + "_placeholder").c_str());
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    auto res = Term::createConstant(fresh);
    placeholders.insert(srt,res);
    return res;
  }
  return placeholders.get(srt);
}

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

Formula* InductionContext::getFormula(TermReplacement& tr, bool opposite) const
{
  CALL("InductionContext::getFormula/1");

  ASS(!_cls.empty());
  auto argLists = FormulaList::empty();
  for (const auto& kv : _cls) {
    auto argList = FormulaList::empty();
    for (const auto& lit : kv.second) {
      auto tlit = tr.transform(lit);
      FormulaList::push(new AtomicFormula(opposite ? Literal::complementaryLiteral(tlit) : tlit), argList);
    }
    FormulaList::push(JunctionFormula::generalJunction(opposite ? Connective::AND : Connective::OR, argList), argLists);
  }
  return JunctionFormula::generalJunction(opposite ? Connective::OR : Connective::AND, argLists);
}

Formula* InductionContext::getFormula(TermList r, bool opposite, Substitution* subst) const
{
  CALL("InductionContext::getFormula/2");

  TermReplacement tr(getPlaceholderForTerm(_indTerm), r);
  if (subst) {
    ASS(r.isVar());
    subst->bind(r.var(), getPlaceholderForTerm(_indTerm));
  }
  return getFormula(tr, opposite);
}

Formula* InductionContext::getFormulaWithSquashedSkolems(TermList r, bool opposite,
  unsigned& var, VList** varList, Substitution* subst) const
{
  CALL("InductionContext::getFormulaWithSquashedSkolems");

  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return getFormula(r, opposite, subst);
  }
  SkolemSquashingTermReplacement tr(getPlaceholderForTerm(_indTerm), r, var);
  unsigned temp = var;
  auto res = getFormula(tr, opposite);
  if (subst) {
    ASS(r.isVar());
    subst->bind(r.var(), getPlaceholderForTerm(_indTerm));
    DHMap<Term*,unsigned>::Iterator it(tr._tv);
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

ContextReplacement::ContextReplacement(const InductionContext& context)
    : TermReplacement(context._indTerm, TermList(getPlaceholderForTerm(context._indTerm))),
      _context(context), _used(false) {}

InductionContext ContextReplacement::next()
{
  CALL("ContextReplacement::next");
  ASS(hasNext());
  InductionContext context(_context._indTerm);
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = transform(lit);
      if (tlit != lit) {
        context.insert(kv.first, tlit);
      }
    }
  }
  _used = true;
  return context;
}

ContextReplacement* ContextSubsetReplacement::instance(const InductionContext& context, const Options& opt)
{
  CALL("ContextSubsetReplacement::instance");
  if (opt.inductionGen()) {
    return new ContextSubsetReplacement(context, opt.maxInductionGenSubsetSize());
  }
  return new ContextReplacement(context);
}

ContextSubsetReplacement::ContextSubsetReplacement(const InductionContext& context, const unsigned maxSubsetSize)
  : ContextReplacement(context), _occurrences(0), _maxSubsetSize(maxSubsetSize), _ready(false)
{
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      _occurrences += lit->countSubtermOccurrences(TermList(_context._indTerm));
    }
  }
  _maxIterations = pow(2, _occurrences);
}

TermList ContextSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("ContextSubsetReplacement::transformSubterm");
  if (trm.isTerm() && trm.term() == _context._indTerm){
    // Replace either if there are too many occurrences to try all possibilities,
    // or if the bit in _iteration corresponding to this match is set to 1.
    if ((_occurrences > _maxOccurrences) || (1 & (_iteration >> _matchCount++))) {
      return _r;
    }
  }
  return trm;
}

bool ContextSubsetReplacement::hasNext()
{
  CALL("ContextSubsetReplacement::hasNext");
  if (_ready) {
    return hasNextInner();
  }
  _ready = true;
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  unsigned setBits = BitUtils::oneBits(_iteration);
  // Skip this iteration if not all bits are set, but more than maxSubset are set.
  while (hasNextInner() &&
         ((_maxSubsetSize > 0) && (setBits < _occurrences) && (setBits > _maxSubsetSize))) {
    _iteration++;
    setBits = BitUtils::oneBits(_iteration);
  }
  if (!hasNextInner() ||
      ((_occurrences > _maxOccurrences) && (_iteration > 1))) {
    // All combinations were already returned.
    return false;
  }
  return true;
}

InductionContext ContextSubsetReplacement::next() {
  CALL("ContextSubsetReplacement::next");
  ASS(_ready);
  InductionContext context(_context._indTerm);
  _matchCount = 0;
  for (const auto& kv : _context._cls) {
    for (const auto& lit : kv.second) {
      auto tlit = transform(lit);
      if (tlit != lit) {
        context.insert(kv.first, tlit);
      }
    }
  }
  _ready = false;
  return context;
}

void Induction::attach(SaturationAlgorithm* salg) {
  CALL("Induction::attach");

  GeneratingInferenceEngine::attach(salg);
  if (InductionHelper::isIntInductionOneOn()) {
    _comparisonIndex = static_cast<LiteralIndex*>(_salg->getIndexManager()->request(UNIT_INT_COMPARISON_INDEX));
    _inductionTermIndex = static_cast<TermIndex*>(_salg->getIndexManager()->request(INDUCTION_TERM_INDEX));
  }
  if (InductionHelper::isNonUnitStructInductionOn()) {
    _structInductionTermIndex = static_cast<TermIndex*>(
      _salg->getIndexManager()->request(STRUCT_INDUCTION_TERM_INDEX));
  }
}

void Induction::detach() {
  CALL("Induction::detach");

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
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise, InductionHelper(_comparisonIndex, _inductionTermIndex), getOptions(),
    _structInductionTermIndex, _formulaIndex));
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

  VirtualIterator<InductionContext> operator()(pair<Term*, VirtualIterator<TermQueryResult>> arg) {
    auto indDepth = _premise->inference().inductionDepth();
    // heuristic 2
    if (indDepth) {
      auto res = VirtualIterator<InductionContext>::getEmpty();
      // check for complex term and non-equality
      if (_lit->isEquality() || !arg.first->arity()) {
        return res;
      }
      while (arg.second.hasNext()) {
        auto tqr = arg.second.next();
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
              !((st1.containsSubterm(st2) && st2.term() == arg.first) ||
                (st2.containsSubterm(st1) && st1.term() == arg.first)))
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
        res = pvi(getConcatenatedIterator(res, getSingletonIterator(ctx)));
      }
      return res;
    // heuristic 1
    } else {
      InductionContext ctx(arg.first, _lit, _premise);
      Set<Literal*> lits;
      lits.insert(_lit);
      while (arg.second.hasNext()) {
        auto tqr = arg.second.next();
        // TODO: having the same literal multiple times has unwanted effects
        // in the clausification/resolution part, so avoid it for now
        if (lits.contains(tqr.literal)) {
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
  CALL("Induction::ClauseIterator::processLiteral");

  if(_opt.showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << lit->toString() << " in " << premise->toString() << endl;
    env.endOutput();
  }

  if (lit->ground()) {
      Set<Term*> ta_terms;
      Set<Term*> int_terms;

      NonVariableNonTypeIterator it(lit);
      while(it.hasNext()){
        Term* ts = it.next();
        unsigned f = ts->functor(); 
        if(InductionHelper::isInductionTermFunctor(f)){
          if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionFunctor(f)){
            ta_terms.insert(ts);
          }
          if(InductionHelper::isIntInductionOneOn() && InductionHelper::isIntInductionTermListInLiteral(ts, lit)){
            int_terms.insert(ts);
          }
        }
      }

    if (InductionHelper::isInductionLiteral(lit)) {
      Set<Term*>::Iterator citer1(int_terms);
      while(citer1.hasNext()){
        Term* t = citer1.next();
        auto leBound = iterTraits(_helper.getLess(t)).collect<Stack>();
        auto grBound = iterTraits(_helper.getGreater(t)).collect<Stack>();
        auto indLitsIt = vi(ContextSubsetReplacement::instance(InductionContext(t, lit, premise), _opt));
        while (indLitsIt.hasNext()) {
          auto ctx = indLitsIt.next();
          // process lower bounds
          for (const auto& b1 : leBound) {
            if (b1.clause == premise) {
              continue;
            }
            if (_helper.isInductionForFiniteIntervalsOn()) {
              // process upper bounds together with current lower bound
              for (const auto& b2 : grBound) {
                if (b2.clause == premise) {
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
              if (b2.clause == premise) {
                continue;
              }
              performInfIntInduction(ctx, false, b2);
            }
          }
          // add formula with default bound
          if (_opt.integerInductionDefaultBound()) {
            InductionFormulaIndex::Entry* e = nullptr;
            static TermQueryResult defaultBound(TermList(theory->representConstant(IntegerConstantType(0))), nullptr, nullptr, ResultSubstitutionSP());
            // for now, represent default bounds with no bound in the index, this is unique
            // since the placeholder is still int
            if (notDoneInt(ctx, nullptr, nullptr, e)) {
              performIntInduction(ctx, e, true, defaultBound, nullptr);
              performIntInduction(ctx, e, false, defaultBound, nullptr);
            }
            resolveClauses(ctx, e, nullptr, nullptr);
          }
        }
      }
    }
    // collect term queries for each induction term
    auto sideLitsIt = VirtualIterator<pair<Term*, TermQueryResultIterator>>::getEmpty();
    if (_opt.nonUnitInduction()) {
      sideLitsIt = pvi(iterTraits(Set<Term*>::Iterator(ta_terms))
        .map([this](Term* arg) {
          return make_pair(arg, _structInductionTermIndex->getGeneralizations(TypedTermList(arg), true));
        }));
    }
    // put clauses from queries into contexts alongside with the given clause and induction term
    auto sideLitsIt2 = iterTraits(sideLitsIt)
      .flatMap(InductionContextFn(premise, lit))
      // generalize all contexts if needed
      .flatMap([this](const InductionContext& arg) {
        return vi(ContextSubsetReplacement::instance(arg, _opt));
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
    auto indCtxSingle = iterTraits(Set<Term*>::Iterator(ta_terms))
      .map([&lit,&premise](Term* arg) {
        return InductionContext(arg, lit, premise);
      })
      // generalize all contexts if needed
      .flatMap([this](const InductionContext& arg) {
        return vi(ContextSubsetReplacement::instance(arg, _opt));
      });
    auto indCtxIt = iterTraits(getConcatenatedIterator(sideLitsIt2, indCtxSingle))
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
      InductionFormulaIndex::Entry* e;
      // generate formulas and add them to index if not done already
      if (_formulaIndex.findOrInsert(ctx, e)) {
        if(one){
          performStructInductionOne(ctx,e);
        }
        if(two){
          performStructInductionTwo(ctx,e);
        }
        if(three){
          performStructInductionThree(ctx,e);
        }
      }
      // resolve the formulas with the premises
      for (auto& kv : e->get()) {
        resolveClauses(kv.first, ctx, kv.second);
      }
    }
  }
}

void InductionClauseIterator::processIntegerComparison(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processIntegerComparison");

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
      .filter([&premise](const TermQueryResult& tqr) {
        return tqr.clause != premise;
      })
      .map([&indt](const auto& tqr) {
        return InductionContext(indt, tqr.literal, tqr.clause);
      })
      .flatMap([this](const InductionContext& arg) {
        return vi(ContextSubsetReplacement::instance(arg, _opt));
      });
    TermQueryResult b(bound, lit, premise, ResultSubstitutionSP());
    // loop over literals containing the current induction term
    while (it.hasNext()) {
      auto ctx = it.next();
      if (_helper.isInductionForFiniteIntervalsOn()) {
        // go over the lower/upper bounds that contain the same induction term as the current bound
        for (const auto& b2 : bound2) {
          if (b2.clause == ctx._cls.begin()->first) {
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

ClauseStack InductionClauseIterator::produceClauses(Formula* hypothesis, InferenceRule rule, const InductionContext& context)
{
  CALL("InductionClauseIterator::produceClauses");
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
    env.beginOutput();
    env.out() << "[Induction] formula " << fu->toString() << endl;
    env.endOutput();
  }
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  switch (rule) {
    case InferenceRule::STRUCT_INDUCTION_AXIOM:
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
void InductionClauseIterator::resolveClauses(InductionContext context, InductionFormulaIndex::Entry* e, const TermQueryResult* bound1, const TermQueryResult* bound2)
{
  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  static TermList ph(getPlaceholderForTerm(context._indTerm));
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
IntUnionFind findDistributedVariants(const Stack<Clause*>& clauses, Substitution& subst, const InductionContext& context)
{
  CALL("findDistributedVariants");
  const auto& toResolve = context._cls;
  IntUnionFind uf(clauses.size());
  for (unsigned i = 0; i < clauses.size(); i++) {
    auto cl = clauses[i];
    Stack<Literal*> conclusionLits(toResolve.size());
#if VDEBUG
    Stack<unsigned> variantCounts(toResolve.size());
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
          if (lit == clit) {
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
      ASS_EQ(variantCounts[k],0);
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
Clause* resolveClausesHelper(const InductionContext& context, const Stack<Clause*>& cls, IntUnionFind::ElementIterator eIt, Substitution& subst, bool generalized, bool applySubst)
{
  CALL("resolveClausesHelper");
  // first create the clause with the required size
  ASS(eIt.hasNext());
  auto cl = cls[eIt.next()];
  unsigned newLength = cl->length();
  auto premises = UnitList::singleton(cl);
  const auto& toResolve = context._cls;
  while (eIt.hasNext()) {
    auto other = cls[eIt.next()];
    ASS_EQ(other->length(),newLength);
    UnitList::push(other,premises);
  }

  for (const auto& kv : toResolve) {
    newLength += kv.first->length() - kv.second.size() - 1;
    UnitList::push(kv.first, premises);
  }

  Inference inf(GeneratingInferenceMany(
    generalized ? InferenceRule::GEN_INDUCTION_HYPERRESOLUTION : InferenceRule::INDUCTION_HYPERRESOLUTION,
    premises));
  Clause* res = new(newLength) Clause(newLength, inf);

  unsigned next = 0;
#if VDEBUG
  unsigned cnt = next;
#endif
  for (unsigned i = 0; i < cl->length(); i++) {
    Literal* curr=(*cl)[i];
    auto clit = SubstHelper::apply<Substitution>(Literal::complementaryLiteral(curr), subst);
    bool contains = false;
    for (const auto& kv : toResolve) {
      for (const auto& lit : kv.second) {
        if (lit == clit) {
          contains = true;
          break;
        }
      }
      if (contains) {
        break;
      }
    }
    if (!contains) {
      ASS(next < newLength);
      if (applySubst) {
        TermReplacement tr(getPlaceholderForTerm(context._indTerm),TermList(context._indTerm));
        (*res)[next] = tr.transform(SubstHelper::apply<Substitution>(curr,subst));
      } else {
        (*res)[next] = curr;
      }
      next++;
    }
  }
  ASS_EQ(next-cnt,cl->length()-toResolve.size());

  for (const auto& kv : toResolve) {
    ASS(cnt = next);
    for (unsigned i = 0; i < kv.first->length(); i++) {
      bool copyCurr = true;
      for (const auto& lit : kv.second) {
        TermReplacement tr(getPlaceholderForTerm(context._indTerm),TermList(context._indTerm));
        auto rlit = tr.transform(lit);
        if (rlit == (*kv.first)[i]) {
          copyCurr = false;
          break;
        }
      }
      if (copyCurr) {
        (*res)[next] = (*kv.first)[i];
        next++;
      }
    }
    ASS_EQ(next-cnt,kv.first->length()-kv.second.size());
  }
  ASS_EQ(next,newLength);

  return res;
}

void InductionClauseIterator::resolveClauses(const ClauseStack& cls, const InductionContext& context, Substitution& subst, bool applySubst)
{
  CALL("InductionClauseIterator::resolveClauses");
  ASS(cls.isNonEmpty());
  bool generalized = false;
  for (const auto& kv : context._cls) {
    for (const auto& lit : kv.second) {
      if (lit->containsSubterm(TermList(context._indTerm))) {
        generalized = true;
        break;
      }
    }
    if (generalized) {
      break;
    }
  }
  if (generalized) {
    env.statistics->generalizedInductionApplication++;
  } else {
    env.statistics->inductionApplication++;
  }

  auto uf = findDistributedVariants(cls, subst, context);
  IntUnionFind::ComponentIterator cit(uf);
  while(cit.hasNext()){
    IntUnionFind::ElementIterator eIt = cit.next();
    _clauses.push(resolveClausesHelper(context, cls, eIt, subst, generalized, applySubst));
    if(_opt.showInduction()){
      env.beginOutput();
      env.out() << "[Induction] generate " << _clauses.top()->toString() << endl;
      env.endOutput();
    }
  }
}

void InductionClauseIterator::performFinIntInduction(const InductionContext& context, const TermQueryResult& lb, const TermQueryResult& ub)
{
  CALL("InductionClauseIterator::performInfIntInduction");
  InductionFormulaIndex::Entry* e = nullptr;
  if (notDoneInt(context, lb.literal, ub.literal, e)) {
    performIntInduction(context, e, true, lb, &ub);
    performIntInduction(context, e, false, ub, &lb);
  }
  resolveClauses(context, e, &lb, &ub);
}

void InductionClauseIterator::performInfIntInduction(const InductionContext& context, bool increasing, const TermQueryResult& bound)
{
  CALL("InductionClauseIterator::performInfIntInduction");
  InductionFormulaIndex::Entry* e = nullptr;
  if (notDoneInt(context, increasing ? bound.literal : nullptr, increasing ? nullptr : bound.literal, e)) {
    performIntInduction(context, e, increasing, bound, nullptr);
  }
  resolveClauses(context, e, increasing ? &bound : nullptr, increasing ? nullptr : &bound);
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
void InductionClauseIterator::performIntInduction(const InductionContext& context, InductionFormulaIndex::Entry* e, bool increasing, const TermQueryResult& bound1, const TermQueryResult* optionalBound2)
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
  Substitution subst;
  Formula* Ly = context.getFormula(y,true,&subst);

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
  if (hasBound2) {
    // Finite interval induction, use two bounds on both x and y.
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
  } else {
    // Infinite interval induction (either with default bound or not), use only one bound on both x and y.
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

  InferenceRule rule =
      isDefaultBound
          ? (increasing ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
          : (increasing ? (hasBound2 ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM : InferenceRule::INT_INF_UP_INDUCTION_AXIOM)
                        : (hasBound2 ? InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));

  auto cls = produceClauses(hyp, rule, context);
  e->add(std::move(cls), std::move(subst));
}

/**
 * Introduce the Induction Hypothesis
 * ( L[base1] & ... & L[basen] & (L[x] => L[c1(x)]) & ... (L[x] => L[cm(x)]) ) => L[x]
 * for some lit ~L[a]
 * and then force binary resolution on L for each resultant clause
 */

void InductionClauseIterator::performStructInductionOne(const InductionContext& context, InductionFormulaIndex::Entry* e)
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
  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++,false), true, var, nullptr, &subst);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(indPremise),
                            Formula::quantify(conclusion));

  auto cls = produceClauses(hypothesis, InferenceRule::STRUCT_INDUCTION_AXIOM, context);
  e->add(std::move(cls), std::move(subst));
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * We produce the clause ~L[x] \/ ?y : L[y] & !z (z subterm y -> ~L[z])
 * and perform resolution with lit L[c]
 */
void InductionClauseIterator::performStructInductionTwo(const InductionContext& context, InductionFormulaIndex::Entry* e)
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

  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(TermList(var++, false), true, var, nullptr, &subst);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  auto cls = produceClauses(hypothesis, InferenceRule::STRUCT_INDUCTION_AXIOM, context);
  e->add(std::move(cls), std::move(subst));
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
void InductionClauseIterator::performStructInductionThree(const InductionContext& context, InductionFormulaIndex::Entry* e)
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

  Substitution subst;
  auto conclusion = context.getFormulaWithSquashedSkolems(x,true,vars,nullptr,&subst);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(conclusion)));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  auto cls = produceClauses(hypothesis, InferenceRule::STRUCT_INDUCTION_AXIOM, context);
  e->add(std::move(cls), std::move(subst));
}

// Whether an induction formula is applicable (or has already been generated)
// is determined by its conclusion part, which is resolved against the literals
// and bounds we induct on. From this point of view, an integer induction formula
// can have one lower bound and/or one upper bound. This function wraps this
// information by adding the bounds and querying the index with the resulting context.
//
// TODO: default bounds are now stored as special cases with no bounds (this makes
// the resolve part easier) but this means some default bound induction formulas
// are duplicates of normal formulas.
bool InductionClauseIterator::notDoneInt(InductionContext context, Literal* bound1, Literal* bound2, InductionFormulaIndex::Entry*& e)
{
  CALL("InductionClauseIterator::notDoneInt");
  TermList ph(getPlaceholderForTerm(context._indTerm));
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

}
