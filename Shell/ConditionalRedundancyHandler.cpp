/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "ConditionalRedundancyHandler.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/DemodulationHelper.hpp"

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

class ConditionalRedundancyHandler::ConstraintIndex
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

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result, const LiteralSet* lits, const SplitSet* splits)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord, lits, splits);
  }

  void insert(const Ordering* ord, ResultSubstitution* subst, bool result, Splitter* splitter,
    OrderingConstraints&& ordCons, const LiteralSet* lits, SplitSet* splits)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
  }

  bool checkAndInsert(const Ordering* ord, ResultSubstitution* subst, bool result, bool doInsert, Splitter* splitter,
    OrderingConstraints&& ordCons, const LiteralSet* lits, const SplitSet* splits)
  {
    ASS(lits);
    // TODO if this correct if we allow non-unit simplifications?
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    if (check(ts, ord, lits, splits)) {
      return false;
    }
    if (doInsert) {
      insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
    }
    return true;
  }

#if VDEBUG
  Clause* _cl;
#endif

  void insert(const Ordering* ord, const TermStack& ts, ConditionalRedundancyEntry* ptr)
  {
    // first try to insert it into an existing container
    if (!isEmpty()) {
      VariantMatcher vm;
      Stack<CodeOp*> firstsInBlocks;

      FlatTerm* ft = FlatTerm::createUnexpanded(ts);
      vm.init(ft, this, &firstsInBlocks);

      if (vm.next()) {
        ASS(vm.op->isSuccess());
        auto entries = vm.op->template getSuccessResult<Entries>();
        entries->comparator->insert(ptr->ordCons, ptr);
        entries->entries.push(ptr);
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

    auto es = new Entries();
    es->comparator = ord->createComparator();
    es->comparator->insert(ptr->ordCons, ptr);
    es->entries.push(ptr);
    code.push(CodeOp::getSuccess(es));

    incorporate(code);
  }

  bool check(const TermStack& ts, const Ordering* ord, const LiteralSet* lits, const SplitSet* splits)
  {
    if (isEmpty()) {
      return false;
    }

    static SubstMatcher matcher;
    struct Applicator : public SubstApplicator {
      TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
    } applicator;

    matcher.init(this, ts);
    Entries* es;
    while ((es = matcher.next()))
    {
      ASS(es->comparator);
      es->comparator->init(&applicator);
      ConditionalRedundancyEntry* e;
      while ((e = static_cast<ConditionalRedundancyEntry*>(es->comparator->next()))) {
        if (!e->active) {
          continue;
        }

        // check AVATAR constraints
        if (!e->splits->isSubsetOf(splits)) {
          continue;
        }

        // check literal conditions
        auto subsetof = e->lits->iter().all([lits,&applicator](Literal* lit) {
          return lits->member(SubstHelper::apply(lit,applicator));
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
          env.statistics->skippedInferencesDueToOrderingConstraints++;
        }
        if (!e->lits->isEmpty()) {
          env.statistics->skippedInferencesDueToLiteralConstraints++;
        }
        if (!e->splits->isEmpty()) {
          env.statistics->skippedInferencesDueToAvatarConstraints++;
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

  ConditionalRedundancyEntry* createEntry(const TermStack& ts, Splitter* splitter, OrderingConstraints&& ordCons, const LiteralSet* lits, SplitSet* splits) const
  {
    auto e = new ConditionalRedundancyEntry();
    Renaming r;
    if (ordCons.isNonEmpty() || !lits->isEmpty()) {
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
    lits->iter().forEach([&ts](Literal* lit) {
      ASS(checkVars(ts,lit));
    });
#endif

    e->lits = LiteralSet::getFromIterator(lits->iter().map([&r](Literal* lit) {
      return r.apply(lit);
    }));

    ASS(splits);
    e->splits = splits;

    if (!splits->isEmpty()) {
      splitter->addConditionalRedundancyEntry(splits, e);
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

    Entries* next()
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
      return op->getSuccessResult<Entries>();
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
      auto es = op->getSuccessResult<Entries>();
      iterTraits(decltype(es->entries)::Iterator(es->entries))
        .forEach([](auto e) {
          e->release();
        });
      delete es;
    }
  }
};

// ConditionalRedundancyHandler

ConditionalRedundancyHandler* ConditionalRedundancyHandler::create(const Options& opts, const Ordering* ord, Splitter* splitter)
{
  if (!opts.conditionalRedundancyCheck()) {
    return new ConditionalRedundancyHandlerImpl</*enabled*/false,false,false,false>(opts,ord,splitter);
  }
  auto ordC = opts.conditionalRedundancyOrderingConstraints();
  // check for av=on here as otherwise we would have to null-check splits inside the handler
  auto avatarC = opts.splitting() && opts.conditionalRedundancyAvatarConstraints();
  auto litC = opts.conditionalRedundancyLiteralConstraints();
  if (ordC) {
    if (avatarC) {
      if (litC) {
        return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
      }
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
    }
    if (litC) {
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
    }
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/true,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
  }
  if (avatarC) {
    if (litC) {
      return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/true>(opts,ord,splitter);
    }
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/true,/*litC*/false>(opts,ord,splitter);
  }
  if (litC) {
    return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/true>(opts,ord,splitter);
  }
  return new ConditionalRedundancyHandlerImpl<true,/*ordC*/false,/*avatarC*/false,/*litC*/false>(opts,ord,splitter);
}

void ConditionalRedundancyHandler::destroyClauseData(Clause* cl)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

void ConditionalRedundancyHandler::destroyAllClauseData()
{
  decltype(clauseData)::Iterator it(clauseData);
  while (it.hasNext()) {
    auto data = it.next();
    delete data;
  }
}

ConditionalRedundancyHandler::ConstraintIndex** ConditionalRedundancyHandler::getDataPtr(Clause* cl, bool doAllocate)
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

DHMap<Clause*,typename ConditionalRedundancyHandler::ConstraintIndex*> ConditionalRedundancyHandler::clauseData;

// ConditionalRedundancyHandlerImpl

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition(
  Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit,
  bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  auto rwLits = LiteralSet::getEmpty();
  if constexpr (litC) {
    rwLits = LiteralSet::getFromIterator(rwClause->iterLits().filter([rwLit](Literal* lit) {
      return lit != rwLit && rwLit->containsAllVariablesOf(lit);
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,!eqIsResult);
    }));
  }

  auto rwSplits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    rwSplits = rwClause->splits();
  }

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  if (eqClDataPtr && !(*eqClDataPtr)->check(_ord, subs, eqIsResult, rwLits, rwSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  auto eqLits = LiteralSet::getEmpty();
  if constexpr (litC) {
    eqLits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit](Literal* lit) {
      return lit != eqLit && eqLit->containsAllVariablesOf(lit);
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,eqIsResult);
    }));
  }

  auto eqSplits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    eqSplits = eqClause->splits();
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/false);
  if (rwClDataPtr && !(*rwClDataPtr)->check(_ord, subs, !eqIsResult, eqLits, eqSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition2(
  Clause* eqClause, Clause* rwClause, bool eqIsResult, ResultSubstitution* subs, TermList rwTermS, TermList tgtTermS) const
{
  if constexpr (!enabled) {
    return true;
  }

  if constexpr (!ordC) {
    return true;
  }

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/false);

  if (eqClDataPtr && ((*eqClDataPtr)->_varSorts.isEmpty() || (*eqClDataPtr)->isEmpty())) {
    eqClDataPtr = nullptr;
  }
  if (rwClDataPtr && ((*rwClDataPtr)->_varSorts.isEmpty() || (*rwClDataPtr)->isEmpty())) {
    rwClDataPtr = nullptr;
  }
  if (!eqClDataPtr && !rwClDataPtr) {
    return true;
  }
  TermStack eqTs;
  if (eqClDataPtr) {
    eqTs = (*eqClDataPtr)->getInstances([&](unsigned v) { return subs->applyTo(TermList::var(v),eqIsResult); });
  }
  TermStack rwTs;
  if (rwClDataPtr) {
    rwTs = (*rwClDataPtr)->getInstances([&](unsigned v) { return subs->applyTo(TermList::var(v),!eqIsResult); });
  }

  static ConstraintIndex::SubstMatcher matcher;
  static struct Applicator : public SubstApplicator {
    TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
  } applicator;

  bool backtracked = false;

  auto checkFn = [&backtracked](ConstraintIndex** index, const TermStack& ts, const TermPartialOrdering* tpo)
  {
    if (!index) {
      return false;
    }
    matcher.init(*index, ts);
    Entries* es;
    while ((es = matcher.next()))
    {
      ASS(es->comparator);
      bool btd;
      if (es->comparator->check(&applicator, tpo, btd)) {
        if (btd) {
          backtracked = true;
        }
        matcher.reset();
        // success
        return true;
      }
    }
    matcher.reset();
    // failure
    return false;
  };

  DHSet<const TermPartialOrdering*> seen;
  OrderingComparator::GreaterIterator git(*_ord, rwTermS, tgtTermS);

  while (git.hasNext()) {
    auto tpo = git.next();

    if (!seen.insert(tpo)) {
      // already checked this tpo, success
      continue;
    }

    // if success, continue
    if (checkFn(eqClDataPtr, eqTs, tpo)) {
      continue;
    }
    if (checkFn(rwClDataPtr, rwTs, tpo)) {
      continue;
    }
    // if failure, return
    return true;
  }

  // struct IdApplicator : SubstApplicator {
  //   TermList operator()(unsigned v) const override { return TermList::var(v); }
  // } idAppl;
  // env.statistics->generalizedInductionApplicationInProof++;
  // ASS_EQ(ordCons.size(),2);
  // OrderingComparator::GreaterIterator git(*_ord, ordCons[0].lhs, ordCons[0].rhs);
  // ConditionalRedundancyIterator sit2(
  //   *OrderingComparator::createForSingleComparison(*_ord, ordCons[1].lhs, ordCons[1].rhs, true));

  // while (git.hasNext()) {
  //   auto tpo = git.next();
  //   sit2.init(tpo, &idAppl);

  //   while (sit2.hasNext()) {
  //     auto [res2,tpo2] = sit2.next();
  //     if (res2 != Ordering::GREATER) {
  //       continue;
  //     }

  //     if (!seen.insert(tpo2)) {
  //       // already checked this tpo, success
  //       continue;
  //     }

  //     // if success, continue
  //     if (checkFn(eqClDataPtr, eqTs, tpo2)) {
  //       continue;
  //     }
  //     if (checkFn(rwClDataPtr, rwTs, tpo2)) {
  //       continue;
  //     }
  //     // if failure, return
  //     return true;
  //   }
  // }

  ASS(backtracked);
  env.statistics->skippedInferencesDueToImpliedOrderingConstraints++;
  env.statistics->skippedSuperposition++;
  return false;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::insertSuperposition(
  Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
  Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return;
  }

  struct Applicator : SubstApplicator {
    Applicator(ResultSubstitution* subst, bool result) : subst(subst) {}
    TermList operator()(unsigned v) const override {
      return subst->apply(TermList::var(v), result);
    }
    ResultSubstitution* subst;
    bool result;
  };

  Applicator appl(subs, !eqIsResult);
  Ordering::Result otherComp;

  auto premiseRedundant = isSuperpositionPremiseRedundant(
    rwClause, rwLitS, rwTermS, tgtTermS, eqClause, eqLHS, &appl, otherComp);

  // create ordering constraints
  OrderingConstraints ordCons;
  if constexpr (ordC) {
    // TODO we cannot handle them together yet
    if (eqComp != Ordering::LESS) {
      if (!rwTermS.containsAllVariablesOf(tgtTermS)) {
        return;
      }
      ordCons.push({ rwTermS, tgtTermS, Ordering::GREATER });
    }
    if (!premiseRedundant) {
      TermList other = EqHelper::getOtherEqualitySide(rwLitS, rwTermS);
      if (otherComp != Ordering::INCOMPARABLE || !other.containsAllVariablesOf(tgtTermS)) {
        return;
      }
      ordCons.push({ other, tgtTermS, Ordering::GREATER });
    }
  } else {
    if (eqComp != Ordering::LESS || !premiseRedundant) {
      return;
    }
  }

  // create literal constraints
  auto lits = LiteralSet::getEmpty();
  if constexpr (litC) {
    if (eqClause->numSelected()!=1) {
      return;
    }
    lits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit,eqLHS](Literal* lit) {
      return lit != eqLit && eqLHS.containsAllVariablesOf(TermList(lit));
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,eqIsResult);
    }));
    if (eqClause->size()>lits->size()+1) {
      return;
    }
  } else {
    if (eqClause->length()!=1) {
      return;
    }
  }

  // create AVATAR constraints
  auto splits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    splits = eqClause->splits()->subtract(rwClause->splits());
  } else {
    if (!eqClause->noSplits()) {
      return;
    }
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/true);
  (*rwClDataPtr)->insert(_ord, subs, !eqIsResult, _splitter, std::move(ordCons), lits, splits);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleResolution(
  Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  // Note that we're inserting into the data of one clause based on the *other* clause
  {
    bool doInsert = resultLit->isPositive();

    // create literal constraints
    auto lits = LiteralSet::getEmpty();
    if constexpr (litC) {
      lits = LiteralSet::getFromIterator(resultCl->iterLits().filter([resultLit](Literal* lit) {
        return lit != resultLit && resultLit->containsAllVariablesOf(lit);
      }).map([subs](Literal* lit) {
        return subs->applyToResult(lit);
      }));
      if (resultCl->numSelected()>1 || resultCl->length()>lits->size()+1) {
        doInsert = false;
      }
    } else {
      if (resultCl->length()!=1) {
        doInsert = false;
      }
    }

    // create AVATAR constraints
    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = resultCl->splits()->subtract(queryCl->splits());
    } else {
      if (!resultCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(
      _ord, subs, /*result*/false, doInsert, _splitter, OrderingConstraints(), lits, splits))
    {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  {
    bool doInsert = queryLit->isPositive();

    // create literal constraints
    auto lits = LiteralSet::getEmpty();
    if constexpr (litC) {
      lits = LiteralSet::getFromIterator(queryCl->iterLits().filter([queryLit](Literal* lit) {
        return lit != queryLit && queryLit->containsAllVariablesOf(lit);
      }).map([subs](Literal* lit) {
        return subs->applyToQuery(lit);
      }));
      if (queryCl->numSelected()>1 || queryCl->length()>lits->size()+1) {
        doInsert = false;
      }
    } else {
      if (queryCl->length()!=1) {
        doInsert = false;
      }
    }

    // create AVATAR constraints
    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = queryCl->splits()->subtract(resultCl->splits());
    } else {
      if (!queryCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(resultCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(
      _ord, subs, /*result*/true, doInsert, _splitter, OrderingConstraints(), lits, splits))
    {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  return true;
}

/**
 * This function is similar to @b DemodulationHelper::isPremiseRedundant.
 * However, here we do not assume that the rewriting equation is unit, which necessitates some additional checks.
 */
template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::isSuperpositionPremiseRedundant(
  Clause* rwCl, Literal* rwLit, TermList rwTerm, TermList tgtTerm, Clause* eqCl, TermList eqLHS,
  const SubstApplicator* eqApplicator, Ordering::Result& tord) const
{
  // if check is turned off, we always report redundant
  if (!_redundancyCheck) {
    return true;
  }

  // if the top-level terms are not involved, premise is redundant
  if (!rwLit->isEquality() || (rwTerm!=*rwLit->nthArgument(0) && rwTerm!=*rwLit->nthArgument(1))) {
    return true;
  }

  // we can only check encompassment demodulation if eqCl is unit
  if (_encompassing && eqCl->length()==1) {
    // if we have a negative literal or non-unit, premise is redundant
    if (rwLit->isNegative() || rwCl->length() != 1) {
      return true;
    }
    // otherwise (we have a positive unit), if substitution is not
    // renaming on side premise, main premise is redundant
    if (!Inferences::DemodulationHelper::isRenamingOn(eqApplicator,eqLHS)) {
      return true;
    }
  }

  // else we do standard redundancy check
  TermList other=EqHelper::getOtherEqualitySide(rwLit, rwTerm);
  tord = _ord->compare(tgtTerm, other);
  return tord == Ordering::LESS;
  // TODO perform ordering check for rest of rwCl
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkEquations(Clause* cl) const
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
    (*clDataPtr)->insert(_ord, rsubs.ptr(), /*result*/false, /*splitter*/nullptr, OrderingConstraints(), LiteralSet::getEmpty(), SplitSet::getEmpty());
  });
}

}
