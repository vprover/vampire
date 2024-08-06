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
 * @file InstanceRedundancyHandler.cpp
 * Implements class InstanceRedundancyHandler.
 */

#include "InstanceRedundancyHandler.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Ordering.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Lib/Environment.hpp"

#include "Statistics.hpp"

namespace Indexing
{

class InstanceRedundancyHandler::SubstitutionCoverTree
  : public CodeTree
{
public:
  SubstitutionCoverTree(Clause* cl) : _varSorts()
  {
    _clauseCodeTree=false;
    for (unsigned i = 0; i < cl->length(); i++) {
      SortHelper::collectVariableSorts((*cl)[i], _varSorts);
    }
  }

  bool checkAndInsert(const Ordering* ord, ResultSubstitution* subst, bool result, bool doInsert=false, Term* lhs=nullptr, Term* rhs=nullptr)
  {
    if (_varSorts.isEmpty()) {
      return true;
    }
    auto ts = getInstances([subst,result](unsigned v) { return subst->applyTo(TermList(v,false),result); });
    if (check(ts, ord)) {
      return false;
    }
    if (doInsert) {
      auto ld = new LeafData();
      if (lhs) {
        ASS(rhs);
        ASS(lhs->containsAllVariablesOf(rhs));
        Renaming r;
        // normalize lhs and rhs, the same way as
        // terms from ts are normalized upon insertion
        for (const auto t : ts) {
          r.normalizeVariables(t);
        }
        ld->lhs = r.apply(lhs);
        ld->rhs = r.apply(rhs);
      } else {
        ASS(!rhs);
        ld->lhs = nullptr;
        ld->rhs = nullptr;
      }
      insert(ts,ld);
    }
    return true;
  }

private:
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

  bool check(const TermStack& ts, const Ordering* ord)
  {
    if (isEmpty()) {
      return false;
    }

    static SubstMatcher matcher;

    matcher.init(this, ts);
    LeafData* ld;
    while ((ld = matcher.next())) {
      if (!ld->lhs) {
        return true;
      }
      if (ord) {
        struct Applicator : public SubstApplicator {
          TermList operator()(unsigned v) const override { return matcher.bindings[v]; }
        } applicator;

        // if (ord->isGreater(TermList(ld->lhs),TermList(ld->rhs),&applicator,ld->comp)) {
        //   return true;
        // }
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

  struct LeafData {
    Term* lhs = nullptr;
    Term* rhs = nullptr;
    OrderingComparatorUP comp;
  };

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

// InstanceRedundancyHandler

DHMap<Clause*,InstanceRedundancyHandler::SubstitutionCoverTree*> InstanceRedundancyHandler::clauseData;

InstanceRedundancyHandler::SubstitutionCoverTree** InstanceRedundancyHandler::getDataPtr(Clause* cl, bool doAllocate)
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

bool InstanceRedundancyHandler::handleSuperposition(Clause* eqClause, Clause* rwClause,
  TermList rwTermS, TermList tgtTermS, TermList eqLHS, Literal* rwLitS, Ordering::Result eqComp,
  bool eqIsResult, ResultSubstitution* subs) const
{
  if (_optVal==Options::InstanceRedundancyCheck::OFF) {
    return true;
  }

  auto eqClDataPtr = getDataPtr(eqClause, /*doAllocate=*/false);
  if (eqClDataPtr && !(*eqClDataPtr)->checkAndInsert(_ord, subs, eqIsResult, /*doInsert=*/false)) {
    env.statistics->skippedSuperposition++;
    return false;
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

  auto doInsert = eqClause->length()==1 && eqClause->noSplits() &&
    ((_optVal!=Options::InstanceRedundancyCheck::LAZY && rwTermS.containsAllVariablesOf(tgtTermS)) || eqComp == Ordering::LESS) &&
    (!_demodulationHelper.redundancyCheckNeededForPremise(rwClause, rwLitS, rwTermS) ||
      // TODO for rwClause->length()!=1 the function isPremiseRedundant does not work yet
      (rwClause->length()==1 && _demodulationHelper.isPremiseRedundant(rwClause, rwLitS, rwTermS, tgtTermS, eqLHS, &appl)));

  bool incompInserted = doInsert && eqComp != Ordering::LESS;
  auto rwClDataPtr = getDataPtr(rwClause, /*doAllocate=*/doInsert);

  if (rwClDataPtr && !(*rwClDataPtr)->checkAndInsert(_ord, subs, !eqIsResult, doInsert,
    incompInserted ? rwTermS.term() : nullptr, incompInserted ? tgtTermS.term() : nullptr))
  {
    env.statistics->skippedSuperposition++;
    return false;
  }
  return true;
}

bool InstanceRedundancyHandler::handleResolution(Clause* queryCl, Literal* queryLit,
  Clause* resultCl, Literal* resultLit,
  ResultSubstitution* subs, const Options& opts, const Ordering* ord)
{
  if (opts.instanceRedundancyCheck()==Options::InstanceRedundancyCheck::OFF) {
    return true;
  }

  // Note that we're inserting into the data of one clause based on the *other* clause
  {
    bool doInsert = resultLit->isPositive() && resultCl->size()==1 && resultCl->noSplits();
    auto dataPtr = getDataPtr(queryCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(ord, subs, false, doInsert)) {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  {
    bool doInsert = queryLit->isPositive() && queryCl->size()==1 && queryCl->noSplits();
    auto dataPtr = getDataPtr(resultCl, /*doAllocate=*/doInsert);
    if (dataPtr && !(*dataPtr)->checkAndInsert(ord, subs, true, doInsert)) {
      env.statistics->skippedResolution++;
      return false;
    }
  }
  return true;
}

bool InstanceRedundancyHandler::handleReductiveUnaryInference(
  Clause* premise, RobSubstitution* subs, const Ordering* ord)
{
  auto dataPtr = getDataPtr(premise, /*doAllocate=*/true);
  auto subst = ResultSubstitution::fromSubstitution(subs, 0, 0);
  if (!(*dataPtr)->checkAndInsert(ord, subst.ptr(), false, /*doInsert=*/true)) {
    return false;
  }
  return true;
}

void InstanceRedundancyHandler::destroyClauseData(Clause* cl)
{
  SubstitutionCoverTree* ptr = nullptr;
  clauseData.pop(cl, ptr);
  delete ptr;
}

}
