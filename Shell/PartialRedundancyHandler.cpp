/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "PartialRedundancyHandler.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Statistics.hpp"

using namespace std;
using namespace Indexing;

namespace Shell
{

template<class T>
bool checkVars(const TermStack& ts, T s)
{
  DHSet<TermList> vars;
  for (const auto& t : ts) {
    VariableIterator vit(t);
    while (vit.hasNext()) {
      vars.insert(vit.next());
    }
  }

  VariableIterator vit(s);
  while (vit.hasNext()) {
    auto var = vit.next();
    if (!vars.contains(var)) {
      return false;
    }
  }
  return true;
}

class PartialRedundancyHandler::ConstraintIndex
  : public CodeTree
{
public:
  ConstraintIndex(Clause* cl) : _varSorts()
  {
    _clauseCodeTree=false;
    _onCodeOpDestroying = onCodeOpDestroying;
#if VDEBUG
    _cl = cl;
#endif
    for (unsigned i = 0; i < cl->length(); i++) {
      SortHelper::collectVariableSorts((*cl)[i], _varSorts);
    }
  }

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result, LiteralSet& lits, const SplitSet* splits)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord, lits, splits);
  }

  void insert(const Ordering* ord, ResultSubstitution* subst, bool result, Splitter* splitter,
    OrderingConstraints&& ordCons, LiteralSet&& lits, SplitSet* splits)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), std::move(lits), splits));
  }

private:
#if VDEBUG
  Clause* _cl;
#endif

  void insert(const Ordering* ord, const TermStack& ts, PartialRedundancyEntry* ptr)
  {
    // first try to insert it into an existing container
    if (!isEmpty()) {
      VariantMatcher vm;
      Stack<CodeOp*> firstsInBlocks;

      FlatTerm* ft = FlatTerm::createUnexpanded(ts);
      vm.init(ft, this, &firstsInBlocks);

      if (vm.next()) {
        ASS(vm.op->isSuccess());
        auto container = vm.op->template getSuccessResult<EntryContainer>();
        container->tod->insert(ptr->ordCons, ptr);
        container->entries.push(ptr);
        ft->destroy();
        return;
      }
      ft->destroy();
    }

    CodeStack code;
    TermCompiler compiler(code);
    for (const auto& t : ts) {
      if (t.isVar()) {
        compiler.handleVar(t.var());
        continue;
      }
      ASS(t.isTerm());
      compiler.handleTerm(t.term());
    }
    compiler.updateCodeTree(this);

    auto es = new EntryContainer();
    es->tod = ord->createTermOrderingDiagram();
    es->tod->insert(ptr->ordCons, ptr);
    es->entries.push(ptr);
    code.push(CodeOp::getSuccess(es));

    incorporate(code);
  }

  bool check(const TermStack& ts, const Ordering* ord, const LiteralSet& lits, const SplitSet* splits)
  {
    if (isEmpty()) {
      return false;
    }

    static SubstMatcher matcher;
    struct Applicator : public SubstApplicator {
      TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
    } applicator;

    matcher.init(this, ts);
    EntryContainer* ec;
    while ((ec = matcher.next()))
    {
      ASS(ec->tod);
      ec->tod->init(&applicator);
      PartialRedundancyEntry* e;
      while ((e = static_cast<PartialRedundancyEntry*>(ec->tod->next()))) {
        if (!e->active) {
          continue;
        }

        // check AVATAR constraints
        if (!e->splits->isSubsetOf(splits)) {
          continue;
        }

        // check literal conditions
        auto subsetof = e->lits.iter().all([&lits,&applicator](Literal* lit) {
          return lits.contains(SubstHelper::apply(lit,applicator));
        });
        if (!subsetof) {
          continue;
        }

        // // check ordering constraints
        // auto ordCons_ok = iterTraits(e->ordCons.iter()).all([ord,&applicator](auto& ordCon) {
        //   return ord->compare(
        //     AppliedTerm(ordCon.lhs,&applicator,true),
        //     AppliedTerm(ordCon.rhs,&applicator,true)) == ordCon.rel;
        // });
        // if (!ordCons_ok) {
        //   INVALID_OPERATION("x");
        // }

        // collect statistics
        if (e->ordCons.isNonEmpty()) {
          env.statistics->inferencesSkippedDueToOrderingConstraints++;
        }
        if (e->lits.size()>0) {
          env.statistics->inferencesSkippedDueToLiteralConstraints++;
        }
        if (!e->splits->isEmpty()) {
          env.statistics->inferencesSkippedDueToAvatarConstraints++;
        }
        matcher.reset();
        return true;
      }
    }
    matcher.reset();
    return false;
  }

  template<class Applicator>
  TermStack getInstances(Applicator applicator) const
  {
    DHMap<unsigned,TermList>::Iterator vit(_varSorts);
    TermStack res;
    while (vit.hasNext()) {
      auto v = vit.nextKey();
      res.push(applicator(v));
    }
    return res;
  }

  DHMap<unsigned,TermList> _varSorts;

  PartialRedundancyEntry* createEntry(const TermStack& ts, Splitter* splitter, OrderingConstraints&& ordCons, LiteralSet&& lits, SplitSet* splits) const
  {
    auto e = new PartialRedundancyEntry();
    Renaming r;
    if (ordCons.isNonEmpty() || lits.size()>0) {
      // normalize constraints, the same way as
      // terms from ts are normalized upon insertion
      for (const auto t : ts) {
        r.normalizeVariables(t);
      }
    }

    for (auto& ordCon : ordCons) {
      ASS(checkVars(ts,ordCon.lhs));
      ASS(checkVars(ts,ordCon.rhs));
      ASS(ordCon.lhs.containsAllVariablesOf(ordCon.rhs));
      ordCon.lhs = r.apply(ordCon.lhs);
      ordCon.rhs = r.apply(ordCon.rhs);
    }
    e->ordCons = std::move(ordCons);

#if VDEBUG
    lits.iter().forEach([&ts](Literal* lit) {
      ASS(checkVars(ts,lit));
    });
#endif

    e->lits.insertFromIterator(lits.iter().map([&r](Literal* lit) {
      return r.apply(lit);
    }));

    ASS(splits);
    e->splits = splits;

    if (!splits->isEmpty()) {
      splitter->addPartialRedundancyEntry(splits, e);
    }

    return e;
  }

  struct SubstMatcher
  : public Matcher
  {
    void init(CodeTree* tree, const TermStack& ts)
    {
      Matcher::init(tree,tree->getEntryPoint());

      ft = FlatTerm::createUnexpanded(ts);

      op=entry;
      tp=0;
    }

    void reset()
    {
      ft->destroy();
    }

    EntryContainer* next()
    {
      if (finished()) {
        //all possible matches are exhausted
        return nullptr;
      }

      _matched=execute();
      if (!_matched) {
        return nullptr;
      }

      ASS(op->isSuccess());
      return op->getSuccessResult<EntryContainer>();
    }
  };

  struct VariantMatcher
  : public RemovingMatcher<true>
  {
  public:
    void init(FlatTerm* ft_, CodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_) {
      RemovingMatcher::init(tree_->getEntryPoint(), 0, 0, tree_, firstsInBlocks_);
      ft=ft_;
      tp=0;
      op=entry;
    }
  };

  static void onCodeOpDestroying(CodeOp* op) {
    if (op->isSuccess()) {
      auto es = op->getSuccessResult<EntryContainer>();
      iterTraits(decltype(es->entries)::Iterator(es->entries))
        .forEach([](auto e) {
          e->release();
        });
      delete es;
    }
  }
};

// PartialRedundancyHandler

PartialRedundancyHandler* PartialRedundancyHandler::create(const Options& opts, const Ordering* ord, Splitter* splitter)
{
  if (!opts.partialRedundancyCheck()) {
    return new PartialRedundancyHandlerImpl</*enabled*/false,false,false,false>(opts,ord,splitter);
  }
  auto ordC = opts.partialRedundancyOrderingConstraints();
  // check for av=on here as otherwise we would have to null-check splits inside the handler
  auto avatarC = opts.splitting() && opts.partialRedundancyAvatarConstraints();
  auto litC = opts.partialRedundancyLiteralConstraints();
  if (ordC) {
    if (avatarC) {
      if (litC) {
        return new PartialRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
      }
      return new PartialRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
    }
    if (litC) {
      return new PartialRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
    }
    return new PartialRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
  }
  if (avatarC) {
    if (litC) {
      return new PartialRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
    }
    return new PartialRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
  }
  if (litC) {
    return new PartialRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
  }
  return new PartialRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
}

void PartialRedundancyHandler::destroyClauseData(Clause* cl)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

PartialRedundancyHandler::ConstraintIndex** PartialRedundancyHandler::getDataPtr(Clause* cl, bool doAllocate)
{
  if (!doAllocate) {
    return clauseData.findPtr(cl);
  }
  ConstraintIndex** ptr;
  clauseData.getValuePtr(cl, ptr, nullptr);
  if (!*ptr) {
    *ptr = new ConstraintIndex(cl);
  }
  return ptr;
}

DHMap<Clause*,typename PartialRedundancyHandler::ConstraintIndex*> PartialRedundancyHandler::clauseData;

// PartialRedundancyHandlerImpl

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition(
  Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit,
  bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  auto rwLits = getRemainingLiterals(rwClause, rwLit, subs, !eqIsResult);
  auto rwSplits = getRemainingSplits(rwClause, eqClause);

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  if (eqClDataPtr && !(*eqClDataPtr)->check(_ord, subs, eqIsResult, rwLits, rwSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  auto eqLits = getRemainingLiterals(eqClause, eqLit, subs, eqIsResult);
  auto eqSplits = getRemainingSplits(eqClause, rwClause);

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/false);
  if (rwClDataPtr && !(*rwClDataPtr)->check(_ord, subs, !eqIsResult, eqLits, eqSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  return true;
}

bool checkOrConstrainGreater(Ordering::Result value, TermList lhs, TermList rhs, OrderingConstraints& cons)
{
  switch (value) {
    case Ordering::GREATER:
      break;
    case Ordering::EQUAL:
    case Ordering::LESS:
      return false;
    case Ordering::INCOMPARABLE: {
      if (!lhs.containsAllVariablesOf(rhs)) {
        return false;
      }
      cons.push({ lhs, rhs, Ordering::GREATER });
      break;
    }
  }
  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::insertSuperposition(
  Clause* eqClause, Clause* rwClause, TermList rwTerm, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
  Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return;
  }

  // create ordering constraints
  OrderingConstraints ordCons;
  // determine whether conclusion is smaller
  if (!checkOrConstrainGreater(Ordering::reverse(eqComp), rwTermS, tgtTermS, ordCons)) {
    return;
  }
  // determine whether side premise is smaller
  if (!compareWithSuperpositionPremise(rwClause, rwLitS, rwTerm, rwTermS, tgtTermS, eqClause, eqLHS, ordCons)) {
    return;
  }
  // don't insert if there are ordering constraints but they are disabled
  if constexpr (!ordC) {
    if (ordCons.isNonEmpty()) {
      return;
    }
  }

  auto lits = getRemainingLiterals(eqClause, eqLit, subs, eqIsResult);
  auto splits = getRemainingSplits(eqClause, rwClause);

  tryInsert(rwClause, subs, !eqIsResult, eqClause, std::move(ordCons), std::move(lits), splits);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleResolution(
  Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  auto resultLits = getRemainingLiterals(resultCl, resultLit, subs, /*result*/true);
  auto resultSplits = getRemainingSplits(resultCl, queryCl);
  auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/false);
  if (dataPtr && !(*dataPtr)->check(_ord, subs, /*result*/false, resultLits, resultSplits)) {
    env.statistics->skippedResolution++;
    return false;
  }

  auto queryLits = getRemainingLiterals(queryCl, queryLit, subs, /*result*/false);
  auto querySplits = getRemainingSplits(queryCl, resultCl);
  dataPtr = getDataPtr(resultCl, /*doAllocate=*/false);
  if (dataPtr && !(*dataPtr)->check(_ord, subs, /*result*/true, queryLits, querySplits)) {
    env.statistics->skippedResolution++;
    return false;
  }

  // Try insertion
  // Note that we're inserting into the data of one clause based on the *other* clause
  if (resultLit->isPositive()) {
    tryInsert(queryCl, subs, /*result*/false, resultCl, OrderingConstraints(), std::move(resultLits), resultSplits);
  } else {
    ASS(queryLit->isPositive());
    tryInsert(resultCl, subs, /*result*/true, queryCl, OrderingConstraints(), std::move(queryLits), querySplits);
  }
  return true;
}

/**
 * This function is similar to @b DemodulationHelper::isPremiseRedundant.
 * However, here we do not assume that the rewriting equation is unit, which necessitates some additional checks.
 */
template<bool enabled, bool ordC, bool avatarC, bool litC>
bool PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::compareWithSuperpositionPremise(
  Clause* rwCl, Literal* rwLitS, TermList rwTerm, TermList rwTermS, TermList tgtTermS, Clause* eqCl, TermList eqLHS, OrderingConstraints& cons) const
{
  // if check is turned off, we always report redundant
  if (!_redundancyCheck) {
    return true;
  }

  // if the top-level terms are not involved, premise is redundant
  if (!rwLitS->isEquality() || (rwTermS!=*rwLitS->nthArgument(0) && rwTermS!=*rwLitS->nthArgument(1))) {
    return true;
  }

  auto other = EqHelper::getOtherEqualitySide(rwLitS, rwTermS);
  const bool canEqEncompass = (eqCl->length() == 1);
  const bool canRwEncompass = (rwLitS->isPositive() && rwCl->length() == 1);

  // we can only check encompassment demodulation if eqCl is unit
  if (_encompassing) {
    if (canEqEncompass) {
      if (!canRwEncompass) {
        return true;
      }
      // both eqClause and rwClause can encompass, check corner cases
      //  l = r      s = t
      // ------------------ σ = mgu(l,s)
      //      (r = t)σ
      // Take grounding substitution θ. Then, (s = t) ⋅ θ is redundant if
      // 1. lθ > rθ, and
      // 2. either
      //    a. s ⊐ l, or
      //    b. l and s are variants, and tθ > rθ, or
      //    c. ¬(l ⊐ s) and sθ > tθ > rθ.

      if (MatchingUtils::matchTerms(eqLHS, rwTerm)) {
        // case 2.a.
        if (!MatchingUtils::matchTerms(rwTerm, eqLHS)) {
          return true;
        }
        // case 2.b.
        return checkOrConstrainGreater(_ord->compare(other, tgtTermS), other, tgtTermS, cons);
      }
      // case 2.c.
      if (!MatchingUtils::matchTerms(rwTerm, eqLHS)) {
        return checkOrConstrainGreater(_ord->compare(rwTermS, other), rwTermS, other, cons)
          && checkOrConstrainGreater(_ord->compare(other, tgtTermS), other, tgtTermS, cons);
      }
      return false;
    }
    if (canRwEncompass) {
      // if rwClause can encompass, it is always smaller than eqClause
      return false;
    }
  }

  // else we perform standard redundancy check
  return checkOrConstrainGreater(_ord->compare(other, tgtTermS), other, tgtTermS, cons);
  // TODO perform ordering check for rest of rwCl
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
LiteralSet PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::getRemainingLiterals(
  Clause* cl, Literal* lit, ResultSubstitution* subs, bool result) const
{
  LiteralSet res;
  if constexpr (litC) {
    res.insertFromIterator(cl->iterLits().filter([lit](Literal* other) {
      return other != lit && lit->containsAllVariablesOf(other);
    }).map([subs,result](Literal* other) {
      return subs->applyTo(other, result);
    }));
  }
  return res;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
const SplitSet* PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::getRemainingSplits(Clause* cl, Clause* other) const
{
  if constexpr (!avatarC) {
    return SplitSet::getEmpty();
  }
  return cl->splits()->subtract(other->splits());
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::tryInsert(
  Clause* into, ResultSubstitution* subs, bool result, Clause* cl, OrderingConstraints&& ordCons, LiteralSet&& lits, SplitSet* splits) const
{
  if constexpr (!enabled) {
    return;
  }

  if (cl->numSelected()!=1 || cl->length()>lits.size()+1) {
    return;
  }
  if constexpr (!avatarC) {
    if (!cl->noSplits()) {
      return;
    }
  }
  auto dataPtr = getDataPtr(into, /*doAllocate=*/true);
  (*dataPtr)->insert(_ord, subs, result, _splitter, std::move(ordCons), std::move(lits), splits);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void PartialRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkEquations(Clause* cl) const
{
  if (!enabled || !ordC) {
    return;
  }

  // TODO disable this when not needed or consider removing it
  cl->iterLits().forEach([cl,this](Literal* lit){
    if (!lit->isEquality() || lit->isNegative()) {
      return;
    }
    auto t0 = lit->termArg(0);
    auto t1 = lit->termArg(1);
    RobSubstitution subs;
    if (!subs.unify(t0,0,t1,0)) {
      return;
    }
    auto clDataPtr = getDataPtr(cl, /*doAllocate=*/true);
    auto rsubs = ResultSubstitution::fromSubstitution(&subs, 0, 0);
    (*clDataPtr)->insert(_ord, rsubs.ptr(), /*result*/false, /*splitter*/nullptr, OrderingConstraints(), LiteralSet(), SplitSet::getEmpty());
  });
}

}
