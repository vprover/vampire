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
 * @file RewritingData.hpp
 * Defines class RewritingData
 *
 */

#ifndef __RewritingData__
#define __RewritingData__

#include "Indexing/ResultSubstitution.hpp"
#include "Indexing/TermIndexingStructure.hpp"

#include "Clause.hpp"
#include "EqHelper.hpp"
#include "TermIterators.hpp"

namespace Kernel {

using namespace Indexing;

class ResultSubstApplicator {
public:
  ResultSubstApplicator(ResultSubstitution* subst, bool eqIsResult) : _subst(subst), _eqIsResult(eqIsResult) {}

  TermList operator()(TermList arg) {
    return _subst->apply(arg, _eqIsResult);
  }

  Literal* operator()(Literal* arg) {
    return _subst->apply(arg, _eqIsResult);
  }

private:
  ResultSubstitution* _subst;
  bool _eqIsResult;
};

struct RuleInfo {
  TermList rhs;
  bool valid = false;
  Term* rwTerm = nullptr;
};

class RewritingData {
public:
  CLASS_NAME(RewritingData);
  USE_ALLOCATOR(RewritingData);

  RewritingData(const Ordering& ord) : _ord(ord) {}

  bool isEmpty() const { return _rules.isEmpty(); }
  bool contains(Term* t) const;
  bool isBlocked(Term* t);
  bool isBlockedUnsafe(Term* t);
  bool isRewritten(Term* t);
  bool blockTerm(Term* t, Term* rwTerm);
  bool addRewrite(Term* t, TermList into, Term* rwTerm);

  void copyRewriteRules(RewritingData* other)
  {
    CALL("RewritingData::copyRewriteRules");
    ASS(isEmpty()); // this can be done only once

    DHMap<Term*,RuleInfo>::Iterator it(other->_rules);
    while (it.hasNext()) {
      Term* lhs;
      RuleInfo info;
      it.next(lhs,info);
      ALWAYS(addRewrite(lhs, info.rhs, info.rwTerm));
    }
  }

  template<class Applicator>
  bool addRewriteRules(Clause* cl, Applicator f, Term* rwTerm = nullptr)
  {
    CALL("RewritingData::addRewriteRules");
    ASS_EQ(cl->store(),Clause::ACTIVE);
    auto other = cl->rewritingData();
    if (!other) {
      return true;
    }

    DHMap<Term*,RuleInfo>::DelIterator it(other->_rules);
    while (it.hasNext()) {
      Term* lhs;
      auto& info = it.nextRef(lhs);
      if (!other->validate(lhs,info)) {
        it.del();
        continue;
      }
      auto rhs = info.rhs;
      lhs = f(TermList(lhs)).term();
      if (!addRewrite(lhs, rhs.isEmpty() ? rhs : f(rhs), rwTerm)) {
        return false;
      }
    }
    return true;
  }

  template<class Applicator>
  bool subsumes(RewritingData* other, Applicator f)
  {
    CALL("RewritingData::subsumes");

    DHMap<Term*,RuleInfo>::DelIterator it(_rules);
    while (it.hasNext()) {
      Term* lhs;
      auto& info = it.nextRef(lhs);
      auto rhs = info.rhs;
      if (!validate(lhs, info)) {
        it.del();
        continue;
      }
      lhs = f(TermList(lhs)).term();
      if (rhs.isNonEmpty()) {
        rhs = f(rhs);
      }
      if (!other) {
        if (rhs.isEmpty()) {
          return false;
        }
      } else {
        auto ptr = other->_rules.findPtr(lhs);
        if (!ptr) {
          if (rhs.isEmpty()) {
            return false;
          }
        } else if (other->validate(lhs, *ptr) && !subsumes(rhs, ptr->rhs)) {
          return false;
        }
      }
    }
    return true;
  }

  inline bool subsumes(TermList rhs, TermList rhsOther) {
    // other is blocked
    if (rhsOther.isEmpty()) {
      return true;
    }
    // this is blocked
    if (rhs.isEmpty()) {
      return false;
    }
    return Ordering::isGorGEorE(_ord.compare(rhsOther,rhs));
  }

  bool blockNewTerms(Clause* cl, ResultSubstitution* subst, bool eqIsResult, Term* rwLhs);
  bool validate(Term* lhs, RuleInfo& info);

  void setClause(Clause* cl) {
    _cl = cl;
  }

  vstring toString() const;

#if VDEBUG
  static void debug(Clause* c) {
    auto rwData = c->rewritingData();
    if (!rwData) {
      return;
    }
    DHMap<Term*,RuleInfo>::Iterator it(rwData->_rules);
    while (it.hasNext()) {
      auto lhs = it.nextKey();
      NonVariableNonTypeIterator nvi(lhs);
      while(nvi.hasNext()) {
        auto st = nvi.next();
        if (!rwData->isBlockedUnsafe(st)) {
          ASS_REP(false,c->toString());
        }
      }
    }
  }
#endif

private:
  DHMap<Term*,RuleInfo> _rules;
  Clause* _cl = nullptr;
  const Ordering& _ord;
  DHSet<unsigned> _vars;
  bool _varsComputed = false;
  LiteralList* _maximalLits = LiteralList::empty();
};

};

#endif /*__RewritingData__*/

