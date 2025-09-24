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

#include "Lib/SharedSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/DemodulationHelper.hpp"
#include "Inferences/Superposition.hpp"

#include "Saturation/Splitter.hpp"

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
  ConstraintIndex(Clause* cl) : _varSorts(), _cl(cl)
  {
    _clauseCodeTree=false;
    _onCodeOpDestroying = onCodeOpDestroying;
    for (unsigned i = 0; i < _cl->length(); i++) {
      SortHelper::collectVariableSorts((*_cl)[i], _varSorts);
    }
  }

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord);
  }

  void insert(const Ordering* ord, Splitter* splitter, ResultSubstitution* subst, bool result, OrderingConstraints&& ordCons, ClauseStack&& cls)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    insert(ord, ts, createEntry(splitter, ts, std::move(ordCons), std::move(cls)));
  }

// private:
  Clause* _cl;

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

  bool check(const TermStack& ts, const Ordering* ord)
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

  PartialRedundancyEntry* createEntry(Splitter* splitter, const TermStack& ts, OrderingConstraints&& ordCons, ClauseStack&& cls) const
  {
    auto e = new PartialRedundancyEntry();
    Renaming r;
    if (ordCons.isNonEmpty()) {
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
    e->cls = std::move(cls);

    if (splitter) {
      auto unionAll = SplitSet::getEmpty();
      for (const auto& cl : e->cls) {
        if (!cl) { continue; }
        unionAll = unionAll->getUnion(cl->splits());
      }
      auto diff = unionAll->subtract(_cl->splits());      
      if (!diff->isEmpty()) {
        splitter->addPartialRedundancyEntry(diff, e);
      }
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

void PartialRedundancyHandler::destroyClauseData(Clause* cl)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

Clause* PartialRedundancyHandler::getGeneratedParent(Clause* cl)
{
  while (isSimplifyingInferenceRule(cl->inference().rule())) {
    switch (cl->inference().rule()) {
      case InferenceRule::FORWARD_DEMODULATION:
      case InferenceRule::SUBSUMPTION_RESOLUTION:
      case InferenceRule::TRIVIAL_INEQUALITY_REMOVAL: {
        auto pit = cl->getParents();
        ALWAYS(pit.hasNext());
        cl = static_cast<Clause*>(pit.next());
        break;
      }
      default: {
        static DHSet<InferenceRule> nothandled;
        if (nothandled.insert(cl->inference().rule())) {
          cout << ruleName(cl->inference().rule()) << " not handled" << endl;
        }
        return cl;
      }
    }
  }
  return cl;
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

bool PartialRedundancyHandler::checkSuperposition(
  Clause* eqClause, Clause* rwClause, ResultSubstitution* subs,
  Literal* rwLitS, TermList rwTermS, TermList tgtTermS, Clause* resClause, DHSet<Clause*>& premiseSet) const
{
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
    eqTs = (*eqClDataPtr)->getInstances([&](unsigned v) { return subs->applyTo(TermList::var(v),true); });
  }
  TermStack rwTs;
  if (rwClDataPtr) {
    rwTs = (*rwClDataPtr)->getInstances([&](unsigned v) { return subs->applyTo(TermList::var(v),false); });
  }

  static ConstraintIndex::SubstMatcher matcher;
  static struct Applicator : public SubstApplicator {
    TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
  } applicator;

  auto afterCheck = [&](void* data) {
    auto e = static_cast<PartialRedundancyEntry*>(data);
    return e->active && !iterTraits(e->cls.iter()).any([&](Clause* cl) { return cl == resClause; });
  };

  Stack<pair<const TermPartialOrdering*, ClauseStack*>> trace;

  TermOrderingDiagram* rwLitTod = nullptr;
  if (rwLitS->isEquality() && _ord->getEqualityArgumentOrder(rwLitS)==Ordering::INCOMPARABLE) {
    auto lhs = rwLitS->termArg(0);
    auto rhs = rwLitS->termArg(1);
    if (!lhs.containsSubterm(rwTermS)) {
      ASS(rhs.containsSubterm(rwTermS));
      rwLitTod = TermOrderingDiagram::createForSingleComparison(*_ord, lhs, rhs);
    } else if (!rhs.containsSubterm(rwTermS)) {
      ASS(lhs.containsSubterm(rwTermS));
      rwLitTod = TermOrderingDiagram::createForSingleComparison(*_ord, rhs, lhs);
    }
  }

  if (rwLitTod) {
    env.statistics->intDBDownInduction++;
  }

  auto checkWrapper = [](TermOrderingDiagram* tod, const SubstApplicator* appl, const TermPartialOrdering* tpo, const std::function<bool(void*)>& afterCheck) {
    // auto data1 = tod->check(appl, tpo, afterCheck);
    auto data2 = tod->check2(appl, tpo, afterCheck);
    // if (data1 != data2) {
    //   INVALID_OPERATION("check is inconsistent");
    // }
    return data2;
  };

  auto checkFn = [&](ConstraintIndex** index, const TermStack& ts, const TermPartialOrdering* tpo)
  {
    if (!index) {
      return false;
    }
    matcher.init(*index, ts);
    EntryContainer* ec;
    while ((ec = matcher.next()))
    {
      ASS(ec->tod);
      void* data;
      if ((data = checkWrapper(ec->tod.get(), &applicator, tpo, afterCheck))) {
        auto e = static_cast<PartialRedundancyEntry*>(data);
        trace.push({ tpo, &e->cls });
        matcher.reset();
        // success
        return true;
      }
    }
    matcher.reset();
    // failure
    return false;
  };

  TermOrderingDiagram::GreaterIterator git(*_ord, rwTermS, tgtTermS);

  // we don't want this to be empty
#if VDEBUG
  bool tpo_found = false;
#endif

  const TermPartialOrdering* tpo;
  while ((tpo = git.next())) {
#if VDEBUG
    tpo_found = true;
#endif

    // if success, continue
    if (checkFn(eqClDataPtr, eqTs, tpo)) {
      continue;
    }
    if (checkFn(rwClDataPtr, rwTs, tpo)) {
      continue;
    }
    if (rwLitTod && checkWrapper(rwLitTod, &idApplicator, tpo, [](void*){ return true; })) {
      env.statistics->intDBDownInductionInProof++;
      continue;
    }
    // if failure, return
    return true;
  }
  ASS(!git.next());
  // TODO this may not be true for LPO
  // ASS(tpo_found);

  // cout << "success for superposition" << endl;
  // cout << "rwClause " << rwClause->toString() << endl;
  // cout << "eqClause " << eqClause->toString() << endl;
  // cout << "resClause " << resClause->toString() << endl;
  for (const auto& [tpo, clsp] : trace) {
    // cout << "for " << *tpo << endl;
    for (const auto& cl : *clsp) {
      ASS_NEQ(cl, resClause);
      if (!cl) { continue; }
      // cout << cl->toString() << endl;
      premiseSet.insert(cl);
    }
  }
  // cout << endl;
  env.statistics->skippedSuperposition++;
  return false;
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

void PartialRedundancyHandler::insertSuperposition(
  Clause* eqClause, Clause* rwClause, TermList rwTerm, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
  Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, ResultSubstitution* subs, Clause* resClause) const
{
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

  tryInsert(rwClause, subs, false, eqClause, std::move(ordCons), resClause);
}

void PartialRedundancyHandler::insertReverseSuperposition(Clause* cl) const
{
  // auto gcl = getGeneratedParent(cl);
  const auto& inf = cl->inference();

  if (inf.rule() != InferenceRule::SUPERPOSITION) {
    return;
  }

  // TODO check that premise did not participate in any simplifications

  auto sup = env.proofExtra.get<Inferences::SuperpositionExtra>(cl);
  UnitIterator it = cl->getParents();
  ALWAYS(it.hasNext());
  auto rwClause = static_cast<Clause*>(it.next());
  ALWAYS(it.hasNext());
  auto eqClause = static_cast<Clause*>(it.next());
  ALWAYS(!it.hasNext());

  // compute unifier for selected literals
  RobSubstitution subst;
  Literal *rwLit = sup.selected.selectedLiteral.selectedLiteral;
  Literal *eqLit = sup.selected.otherLiteral;
  TermList eqLHS = sup.rewrite.lhs;
  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList rwTerm = sup.rewrite.rewritten;
  ASS(eqLit->isEquality());
  ASS(eqLit->isPositive());
  ASS(eqLit->termArg(0) == eqLHS || eqLit->termArg(1) == eqLHS);
  ALWAYS(subst.unify(rwTerm, 0, eqLHS, 1));

  auto rwTermS = subst.apply(rwTerm, 0);
  auto tgtTermS = subst.apply(tgtTerm, 1);
  auto rwLitS = subst.apply(rwLit, 0);
  auto comp = _ord->compare(tgtTermS,rwTermS);

  auto rsubst = ResultSubstitution::fromSubstitution(&subst, 0, 1);

  if ((rwLitS->termArg(0).containsSubterm(rwTermS) && rwTermS != rwLitS->termArg(0)) ||
      (rwLitS->termArg(1).containsSubterm(rwTermS) && rwTermS != rwLitS->termArg(1)))
  {
    return;
  }

  OrderingConstraints ordCons;
  // determine whether conclusion is smaller
  if (!checkOrConstrainGreater(comp, tgtTermS, rwTermS, ordCons)) {
    return;
  }

  RobSubstitution esubst;
  auto ersubst = ResultSubstitution::fromSubstitution(&esubst, 0, 1);
  tryInsert(cl, ersubst.ptr(), false, eqClause, std::move(ordCons), rwClause);
  env.statistics->generalizedInductionApplication++;
  // auto dataPtr = getDataPtr(cl, /*doAllocate=*/true);
  // cout << cl->toString() << endl;
  // cout << *(*dataPtr) << endl;
  // INVALID_OPERATION("x");
}

bool PartialRedundancyHandler::handleResolution(
  Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs, Clause* resClause) const
{
  auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/false);
  if (dataPtr && !(*dataPtr)->check(_ord, subs, /*result*/false)) {
    env.statistics->skippedResolution++;
    return false;
  }

  dataPtr = getDataPtr(resultCl, /*doAllocate=*/false);
  if (dataPtr && !(*dataPtr)->check(_ord, subs, /*result*/true)) {
    env.statistics->skippedResolution++;
    return false;
  }

  // Try insertion
  // Note that we're inserting into the data of one clause based on the *other* clause
  if (resultLit->isPositive()) {
    if (resultCl->length()==1) {
      tryInsert(queryCl, subs, /*result*/false, resultCl, OrderingConstraints(), resClause);
    }
  } else {
    ASS(queryLit->isPositive());
    if (queryCl->length()==1) {
      tryInsert(resultCl, subs, /*result*/true, queryCl, OrderingConstraints(), resClause);
    }
  }
  return true;
}

/**
 * This function is similar to @b DemodulationHelper::isPremiseRedundant.
 * However, here we do not assume that the rewriting equation is unit, which necessitates some additional checks.
 */
bool PartialRedundancyHandler::compareWithSuperpositionPremise(
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

void PartialRedundancyHandler::tryInsert(
  Clause* into, ResultSubstitution* subs, bool result, Clause* cl, OrderingConstraints&& ordCons, Clause* res) const
{
  if (cl->length()!=1) {
    return;
  }
  auto dataPtr = getDataPtr(into, /*doAllocate=*/true);
  (*dataPtr)->insert(_ord, _splitter, subs, result, std::move(ordCons), { cl, res });
}

void PartialRedundancyHandler::checkEquations(Clause* cl) const
{
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
    (*clDataPtr)->insert(_ord, _splitter, rsubs.ptr(), /*result*/false, OrderingConstraints(), ClauseStack());
  });
}

}
