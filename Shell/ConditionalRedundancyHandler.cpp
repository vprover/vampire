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
 * @file ConditionalRedundancyHandler.cpp
 * Implements class ConditionalRedundancyHandler.
 */

#include "ConditionalRedundancyHandler.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"

#include "Statistics.hpp"

using namespace std;
using namespace Indexing;

using LiteralSet = SharedSet<Literal*>;

namespace Shell
{

class ConditionalRedundancyHandler::SubstitutionCoverTree
  : public CodeTree
{
public:
  SubstitutionCoverTree(Clause* cl) : _varSorts()
  {
    _clauseCodeTree=false;
#if VDEBUG
    _cl = cl;
#endif

#if LOG_LEAVES
    _printLeaf = [](ostream& str, const CodeOp* op) {
      auto ld = op->getSuccessResult<LeafData>();
      str << Splitter::splitsToString(ld->splits) << ", ts " << ld->splits_ts;
      ld->lits->iter().forEach([&str](Literal* lit) {
        str << " " << *lit;
      });
      if (ld->comp) {
        str << " " << ld->comp->toString();
      }
    };
#endif
    for (unsigned i = 0; i < cl->length(); i++) {
      SortHelper::collectVariableSorts((*cl)[i], _varSorts);
    }
  }

  bool check(const Ordering* ord, ResultSubstitution* subst, bool result, const LiteralSet* lits, const Splitter* splitter, SplitSet*& blockingSplits)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    return !check(ts, ord, lits, splitter, blockingSplits);
  }

  void insert(ResultSubstitution* subst, bool result, const LiteralSet* lits, const Splitter* splitter, SplitSet* splits, Term* lhs=nullptr, Term* rhs=nullptr)
  {
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList::var(v),result); });
    auto ld = createEntry(ts, lhs, rhs, lits, splitter, splits);
    insert(ts,ld);
  }

  bool checkAndInsert(const Ordering* ord, ResultSubstitution* subst, bool result, const LiteralSet* lits, const Splitter* splitter, SplitSet*& blockingSplits, bool doInsert, SplitSet* splits, Term* lhs=nullptr, Term* rhs=nullptr)
  {
    ASS(lits);
    // TODO if this correct if we allow non-unit simplifications?
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList(v,false),result); });
    if (check(ts, ord, lits, splitter, blockingSplits)) {
      return false;
    }
    if (doInsert) {
      auto ld = createEntry(ts, lhs, rhs, lits, splitter, splits);
      insert(ts,ld);
    }
    return true;
  }

private:
#if VDEBUG
  Clause* _cl;
#endif

  void insert(const TermStack& ts, void* ptr)
  {
    static CodeStack code;
    code.reset();

    static CompileContext cctx;
    cctx.init();
    for (const auto& t : ts) {
      if (t.isVar()) {
        unsigned var=t.var();
        unsigned* varNumPtr;
        if (cctx.varMap.getValuePtr(var,varNumPtr)) {
          *varNumPtr=cctx.nextVarNum++;
          code.push(CodeOp::getTermOp(ASSIGN_VAR, *varNumPtr));
        }	else {
          code.push(CodeOp::getTermOp(CHECK_VAR, *varNumPtr));
        }
      }
      else {
        ASS(t.isTerm());
        compileTerm(t.term(), code, cctx, false);
      }
    }
    cctx.deinit(this);

    // just put anything non-null in there to get a valid success
    code.push(CodeOp::getSuccess(ptr));
    incorporate(code);
  }

  bool check(const TermStack& ts, const Ordering* ord, const LiteralSet* lits, const Splitter* splitter, SplitSet*& blockingSplits)
  {
    if (isEmpty()) {
      return false;
    }

    static SubstMatcher matcher;
    struct Applicator : public SubstApplicator {
      TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
    } applicator;

    matcher.init(this, ts);
    LeafData* ld;
    while ((ld = matcher.next())) {

      // check literal conditions
      auto subsetof = ld->lits->iter().all([lits,&applicator](Literal* lit) {
        return lits->member(SubstHelper::apply(lit,applicator));
      });
      if (!subsetof) {
        continue;
      }

      // check ordering constraints
      if (ld->lhs) {
        if (!ord || !ord->isGreater(TermList(ld->lhs),TermList(ld->rhs),&applicator,ld->comp)) {
          continue;
        }
      }

      // check AVATAR constraints
      if (splitter && !splitter->allSplitLevelsActivatedBefore(ld->splits,ld->splits_ts)) {
        continue;
      }
      blockingSplits = ld->splits;

      // collect statistics
      if (ld->lhs) {
        env.statistics->skippedInferencesDueToOrderingConstraints++;
      }
      if (!ld->lits->isEmpty()) {
        env.statistics->skippedInferencesDueToLiteralConstraints++;
      }
      if (!ld->splits->isEmpty()) {
        env.statistics->skippedInferencesDueToAvatarConstraints++;
      }
      return true;
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

  struct LeafData {
    Term* lhs = nullptr;
    Term* rhs = nullptr;
    OrderingComparatorUP comp;
    const LiteralSet* lits;
    SplitSet* splits = nullptr;
    unsigned splits_ts;
  };

  LeafData* createEntry(const TermStack& ts, Term* lhs, Term* rhs, const LiteralSet* lits, const Splitter* splitter, SplitSet* splits) const
  {
    auto ld = new LeafData();
    Renaming r;
    if (lhs || !lits->isEmpty()) {
      // normalize constraints, the same way as
      // terms from ts are normalized upon insertion
      for (const auto t : ts) {
        r.normalizeVariables(t);
      }
    }

    ASS_EQ(!lhs,!rhs); // we are interested in the "null-ptrness"
    ASS(!lhs || lhs->containsAllVariablesOf(rhs));
    ld->lhs = lhs ? r.apply(lhs) : nullptr;
    ld->rhs = lhs ? r.apply(rhs) : nullptr;
  
    ld->lits = LiteralSet::getFromIterator(lits->iter().map([&r](Literal* lit) {
      return r.apply(lit);
    }));

    ASS(splits);
    ld->splits = splits;
    if (splitter) {
      ld->splits_ts = splitter->getTimestamp();
    }
  
    return ld;
  }

  struct SubstMatcher
  : public Matcher
  {
    void init(CodeTree* tree, const TermStack& ts)
    {
      Matcher::init(tree,tree->getEntryPoint());

      linfos=0;
      linfoCnt=0;

      ft = FlatTerm::createUnexpanded(ts);

      op=entry;
      tp=0;
    }

    void reset()
    {
      ft->destroy();
    }

    LeafData* next()
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
      return op->getSuccessResult<LeafData>();
    }
  };
};

// ConditionalRedundancyHandler

ConditionalRedundancyHandler* ConditionalRedundancyHandler::create(const Options& opts, const Ordering* ord, const Splitter* splitter)
{
  if (!opts.conditionalRedundancyCheck()) {
    return new ConditionalRedundancyHandlerImpl</*enabled*/false,false,false,false>(opts,ord,splitter);
  }
  auto ordC = opts.conditionalRedundancyOrderingConstraints();
  auto avatarC = opts.conditionalRedundancyAvatarConstraints();
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
  SubstitutionCoverTree* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

void ConditionalRedundancyHandler::checkEquations(Clause* cl) const
{
  cl->iterLits().forEach([cl](Literal* lit){
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
    (*clDataPtr)->insert(rsubs.ptr(), false, LiteralSet::getEmpty(), nullptr, SplitSet::getEmpty());
  });
}

ConditionalRedundancyHandler::SubstitutionCoverTree** ConditionalRedundancyHandler::getDataPtr(Clause* cl, bool doAllocate)
{
  if (!doAllocate) {
    return clauseData.findPtr(cl);
  }
  SubstitutionCoverTree** ptr;
  clauseData.getValuePtr(cl, ptr, nullptr);
  if (!*ptr) {
    *ptr = new SubstitutionCoverTree(cl);
  }
  return ptr;
}

DHMap<Clause*,typename ConditionalRedundancyHandler::SubstitutionCoverTree*> ConditionalRedundancyHandler::clauseData;

// ConditionalRedundancyHandlerImpl

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::checkSuperposition(
  Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit,
  bool eqIsResult, ResultSubstitution* subs, SplitSet*& blockingSplits) const
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

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  if (eqClDataPtr && !(*eqClDataPtr)->check(_ord, subs, eqIsResult, rwLits, _splitter, blockingSplits)) {
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

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/false);
  if (rwClDataPtr && !(*rwClDataPtr)->check(_ord, subs, !eqIsResult, eqLits, _splitter, blockingSplits)) {
    env.statistics->skippedSuperposition++;
    return false;
  }

  return true;
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

  auto doInsert =
    // TODO this demodulation redundancy check could be added as constraints
    (!_demodulationHelper.redundancyCheckNeededForPremise(rwClause, rwLitS, rwTermS) ||
      // TODO for rwClause->length()!=1 the function isPremiseRedundant does not work yet
      (rwClause->length()==1 && _demodulationHelper.isPremiseRedundant(rwClause, rwLitS, rwTermS, tgtTermS, eqLHS, &appl)));

  if (!doInsert) {
    return;
  }

  // if the equation is not oriented, consider adding ordering constraints
  if (eqComp != Ordering::LESS && !(ordC && rwTermS.containsAllVariablesOf(tgtTermS))) {
    return;
  }

  auto lits = LiteralSet::getEmpty();
  if constexpr (litC) {
    if (eqClause->numSelected()!=1) {
      return;
    }
    lits = LiteralSet::getFromIterator(eqClause->iterLits().filter([eqLit](Literal* lit) {
      return lit != eqLit && eqLit->containsAllVariablesOf(lit);
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

  auto splits = SplitSet::getEmpty();
  if constexpr (avatarC) {
    splits = eqClause->splits();
  } else {
    if (!eqClause->noSplits()) {
      return;
    }
  }

  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/true);

  (*rwClDataPtr)->insert(subs, !eqIsResult, lits, _splitter, splits,
    eqComp != Ordering::LESS ? rwTermS.term() : nullptr,
    eqComp != Ordering::LESS ? tgtTermS.term() : nullptr);
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleResolution(
  Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs, SplitSet*& blockingSplits) const
{
  if constexpr (!enabled) {
    return true;
  }

  // Note that we're inserting into the data of one clause based on the *other* clause
  {
    bool doInsert = resultLit->isPositive();

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

    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = resultCl->splits();
    } else {
      if (!resultCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(_ord, subs, false, lits, _splitter, blockingSplits, doInsert, splits)) {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  {
    bool doInsert = queryLit->isPositive();

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

    auto splits = SplitSet::getEmpty();
    if constexpr (avatarC) {
      splits = queryCl->splits();
    } else {
      if (!queryCl->noSplits()) {
        doInsert = false;
      }
    }

    auto dataPtr = getDataPtr(resultCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(_ord, subs, true, lits, _splitter, blockingSplits, doInsert, splits)) {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  return true;
}

template<bool enabled, bool ordC, bool avatarC, bool litC>
bool ConditionalRedundancyHandlerImpl<enabled, ordC, avatarC, litC>::handleReductiveUnaryInference(
  Clause* premise, RobSubstitution* subs, SplitSet*& blockingSplits) const
{
  if constexpr (!enabled) {
    return true;
  }
  auto dataPtr = getDataPtr(premise, /*doAllocate=*/true);
  auto subst = ResultSubstitution::fromSubstitution(subs, 0, 0);
  auto lits = LiteralSet::getEmpty();
  auto splits = SplitSet::getEmpty();
  if (!(*dataPtr)->checkAndInsert(_ord, subst.ptr(), false, lits, _splitter, blockingSplits, /*doInsert=*/true, splits)) {
    // TODO fix this by calling Splitter from each calling inference
    if (!blockingSplits->isEmpty()) {
      return true;
    }
    return false;
  }
  return true;
}

}
