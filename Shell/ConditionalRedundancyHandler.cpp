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

std::ostream& operator<<(std::ostream& str, const ConditionalRedundancyEntry& e)
{
  if (!e.active) {
    str << "not active";
  } else {
    str << *e.splits << "; " << *e.lits << "; ";
#if DEBUG_ORDERING
    iterTraits(e.ordCons.iter()).forEach([&str](const Ordering::Constraint& con) {
      str << con;
    });
#endif
  }
  return str;
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

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result, const OrderingConstraints& ordCons, const LiteralSet* lits, const SplitSet* splits)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord, ordCons, lits, splits);
  }

  bool insert(const Ordering* ord, ResultSubstitution* subst, bool result, Splitter* splitter,
    OrderingConstraints&& ordCons, const LiteralSet* lits, SplitSet* splits)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
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
    if (check(ts, ord, ordCons, lits, splits)) {
      return false;
    }
    if (doInsert) {
      return insert(ord, ts, createEntry(ts, splitter, std::move(ordCons), lits, splits));
    }
    return true;
  }

#if VDEBUG
  Clause* _cl;
#endif

  bool insert(const Ordering* ord, Entries* entries, ConditionalRedundancyEntry* ptr)
  {
    ASS(ptr->active);

    ASS(entries->comparator);

    entries->entries.push(ptr);
    entries->comparator->insert(ptr->ordCons);
    return true;
  }

  bool insert(const Ordering* ord, const TermStack& ts, ConditionalRedundancyEntry* ptr)
  {
    CodeStack code;
#define LINEARIZE 1
#if LINEARIZE
    Compiler<false, true> compiler(code);
#else
    TermCompiler compiler(code);
#endif
    for (const auto& t : ts) {
      if (t.isVar()) {
        compiler.handleVar(t.var());
        continue;
      }
      ASS(t.isTerm());
      compiler.handleTerm(t.term());
    }
    for (const auto& [x,y] : compiler.eqCons) {
      ptr->ordCons.push({ TermList::var(x), TermList::var(y), Ordering::EQUAL });
    }
    compiler.updateCodeTree(this);

    auto es = new Entries();
    es->entries.push(ptr);
    es->comparator = ord->createComparator();
    es->comparator->insert(ptr->ordCons);
    code.push(CodeOp::getSuccess(es));

#if LINEARIZE
    if (!isEmpty()) {
      VariantMatcher vm;
      Stack<CodeOp*> firstsInBlocks;

      FlatTerm* ft = FlatTerm::create(ts);
      vm.init(ft, this, &firstsInBlocks);

      if (vm.next()) {
        ASS(vm.op->isSuccess());
        auto es = vm.op->template getSuccessResult<Entries>();
        ft->destroy();
        return insert(ord, es, ptr);
      }
      ft->destroy();
    }
#endif

    incorporate(code);
    return true;
  }

  bool check(const TermStack& ts, const Ordering* ord, const OrderingConstraints& ordCons, const LiteralSet* lits, const SplitSet* splits)
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
      auto res = es->comparator->check(&applicator);
#if DEBUG_ORDERING
      auto ordCons_crosscheck = iterTraits(es->entries.iter()).any([ord,&applicator](auto e) {
        return iterTraits(e->ordCons.iter()).all([ord,&applicator](auto& ordCon) {
          return ord->compare(AppliedTerm(ordCon.lhs,&applicator,true),AppliedTerm(ordCon.rhs,&applicator,true))==ordCon.rel;
        });
      });
      if (res != ordCons_crosscheck) {
        cout << res << " " << ordCons_crosscheck << endl;
        cout << *es->comparator << endl;
        for (const auto& e : es->entries) {
          cout << *e << endl;
        }
        INVALID_OPERATION("conditional redundancy ordering check mismatch");
      }
#endif
      if (res) {
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
  : public RemovingMatcher
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
      iterTraits(decltype(es->entries)::Iterator(es->entries)).forEach([](ConditionalRedundancyEntry* e) { delete e; });
      delete es;
    }
  }

  std::string leafToString(const CodeOp* op) const override {
    std::stringstream str;
    ASS(op->isSuccess());
    auto es = op->getSuccessResult<Entries>();
    str << *es->comparator;
    return str.str();
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

void ConditionalRedundancyHandler::transfer(Clause* from, Clause* to)
{
  ConstraintIndex* ptr = nullptr;
  clauseData.pop(from, ptr);
  if (!ptr) {
    return;
  }
  ALWAYS(clauseData.insert(to, ptr));
}

DHMap<Clause*,typename ConditionalRedundancyHandler::ConstraintIndex*> ConditionalRedundancyHandler::clauseData;

// ConditionalRedundancyHandlerImpl

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition(
  Clause* eqClause, Literal* eqLit, TermList eqLHS, Clause* rwClause, Literal* rwLit,
  bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }

  if (eqClause->redundant() || rwClause->redundant()) {
    env.statistics->skippedSuperposition++;
    return false;
  }
  if (eqClause->ltrRedundant() && eqLHS == eqLit->termArg(0)) {
    env.statistics->skippedSuperposition++;
    return false;
  }
  if (eqClause->rtlRedundant() && eqLHS == eqLit->termArg(1)) {
    env.statistics->skippedSuperposition++;
    return false;
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
  if (eqClDataPtr && !(*eqClDataPtr)->check(_ord, subs, eqIsResult, OrderingConstraints(), rwLits, rwSplits)) {
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
  if (rwClDataPtr && !(*rwClDataPtr)->check(_ord, subs, !eqIsResult, OrderingConstraints(), eqLits, eqSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::insertSuperposition(
  Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
  Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
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
        return true;
      }
      ordCons.push({ rwTermS, tgtTermS, Ordering::GREATER });
    }
    if (!premiseRedundant) {
      TermList other = EqHelper::getOtherEqualitySide(rwLitS, rwTermS);
      if (otherComp != Ordering::INCOMPARABLE || !other.containsAllVariablesOf(tgtTermS)) {
        return true;
      }
      ordCons.push({ other, tgtTermS, Ordering::GREATER });
    }
  } else {
    if (eqComp != Ordering::LESS || !premiseRedundant) {
      return true;
    }
  }

  // create literal constraints
  auto lits = LiteralSet::getEmpty();
  if constexpr (litC) {
    if (eqClause->numSelected()!=1) {
      return true;
    }
    lits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit,eqLHS](Literal* lit) {
      return lit != eqLit && eqLHS.containsAllVariablesOf(TermList(lit));
    }).map([subs,eqIsResult](Literal* lit) {
      return subs->applyTo(lit,eqIsResult);
    }));
    if (eqClause->size()>lits->size()+1) {
      return true;
    }
  } else {
    if (eqClause->length()!=1) {
      return true;
    }
  }

  // create AVATAR constraints
  auto splits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    splits = eqClause->splits()->subtract(rwClause->splits());
  } else {
    if (!eqClause->noSplits()) {
      return true;
    }
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/true);
  if (!(*rwClDataPtr)->insert(_ord, subs, !eqIsResult, _splitter, std::move(ordCons), lits, splits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }
  return true;
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

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleReductiveUnaryInference(
  Clause* premise, RobSubstitution* subs) const
{
  if constexpr (!enabled) {
    return true;
  }
  auto dataPtr = getDataPtr(premise, /*doAllocate=*/true);
  auto subst = ResultSubstitution::fromSubstitution(subs, 0, 0);
  auto lits = LiteralSet::getEmpty();
  auto splits = SplitSet::getEmpty();
  if (!(*dataPtr)->checkAndInsert(
    _ord, subst.ptr(), /*result*/false, /*doInsert=*/true, _splitter, OrderingConstraints(), lits, splits))
  {
    return false;
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
  ASS(enabled);

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
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::initWithEquation(Clause* resClause, TermList rwTerm, TermList tgtTerm) const
{
  if (!enabled) {
    return;
  }

  if (!ordC) {
    return;
  }

  if (!tgtTerm.containsAllVariablesOf(rwTerm)) {
    return;
  }
  OrderingConstraints ordCons;
  ordCons.push({ tgtTerm, rwTerm, Ordering::GREATER });
  auto lits = LiteralSet::getEmpty();
  auto splits = SplitSet::getEmpty();

  struct RenamingSubstitution : public ResultSubstitution {
    TermList applyTo(TermList t, unsigned index) override { return t; }
    void output(std::ostream&) const override {}
  } subst;

  auto clDataPtr = getDataPtr(resClause, /*doAllocate=*/true);
  (*clDataPtr)->insert(_ord, &subst, true, _splitter, std::move(ordCons), lits, splits);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkEquations(Clause* cl) const
{
  if (!enabled) {
    return;
  }

  // TODO return if not enabled
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

template<bool enabled, bool ordC, bool avatarC, bool litC>
void ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSubsumption(Clause* cl) const
{
  if (!enabled) {
    return;
  }

  auto clDataPtr = getDataPtr(cl, /*doAllocate=*/false);
  if (!clDataPtr) {
    return;
  }

  if (cl->redundant()) {
    return;
  }

  struct Applicator : public SubstApplicator {
    TermList operator()(unsigned v) const override { return TermList::var(v); }
  } appl;

  auto ts = (*clDataPtr)->getInstances(appl);
  if ((*clDataPtr)->isEmpty()) {
    return;
  }

  static ConstraintIndex::SubstMatcher matcher;
  matcher.init((*clDataPtr), ts);
  Entries* es = matcher.next();
  matcher.reset();
  // there can be only one such matching currently
  if (!es) {
    return;
  }
  ASS(es->comparator);
  auto subs = static_cast<OrderingComparator::Subsumption*>(cl->redundantSubs());
  if (!subs) {
    subs = new OrderingComparator::Subsumption(*es->comparator.get(), *_ord, OrderingConstraints(), /*ground=*/true);
    cl->setRedundantSubs(subs);
  }
  // cout << "checking redundancy of " << *cl << endl;
  if (subs->check()) {
    cl->markRedundant();
    env.statistics->generalizedInductionApplication++;
    if (cl->ltrRedundant() || cl->rtlRedundant()) {
      // cout << "became fully redundant " << *cl << endl;
    }
    return;
  }
  if (_ord->compare((*cl)[0]->termArg(0),(*cl)[0]->termArg(1))!=Ordering::INCOMPARABLE) {
    return;
  }

  auto subsLtr = static_cast<OrderingComparator::Subsumption*>(cl->ltrRedundantSubs());
  auto subsRtl = static_cast<OrderingComparator::Subsumption*>(cl->rtlRedundantSubs());
  if (!subsLtr || !subsRtl) {
    Renaming r;
    for (const auto t : ts) {
      r.normalizeVariables(t);
    }
    auto lhs = r.apply((*cl)[0]->termArg(0));
    auto rhs = r.apply((*cl)[0]->termArg(1));
    if (!subsLtr) {
      subsLtr = new OrderingComparator::Subsumption(*es->comparator.get(), *_ord, { { lhs, rhs, Ordering::GREATER } }, /*ground=*/true);
      cl->setLtrRedundantSubs(subsLtr);
    }
    if (!subsRtl) {
      subsRtl = new OrderingComparator::Subsumption(*es->comparator.get(), *_ord, { { rhs, lhs, Ordering::GREATER } }, /*ground=*/true);
      cl->setRtlRedundantSubs(subsRtl);
    }
  }
  if (!cl->ltrRedundant()) {
    // cout << "checking redundancy of " << (*cl)[0]->termArg(0) << " -> " << (*cl)[0]->termArg(1) << endl;
    if (subsLtr->check()) {
      env.statistics->generalizedInductionApplicationInProof++;
      // cout << "redundant " << (*cl)[0]->termArg(0) << " -> " << (*cl)[0]->termArg(1) << endl;
      cl->markLtrRedundant();
    }
  }
  if (!cl->rtlRedundant()) {
    // cout << "checking redundancy of " << (*cl)[0]->termArg(1) << " -> " << (*cl)[0]->termArg(0) << endl;
    if (subsRtl->check()) {
      env.statistics->generalizedInductionApplicationInProof++;
      // cout << "redundant " << (*cl)[0]->termArg(1) << " -> " << (*cl)[0]->termArg(0) << endl;
      cl->markRtlRedundant();
    }
  }
}

}
