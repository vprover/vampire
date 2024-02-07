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
  // Term* rwTerm = nullptr;
};

class RewritingData {
public:
  USE_ALLOCATOR(RewritingData);

  RewritingData(const Ordering& ord) : _ord(ord) {}

  bool isEmpty() const { return _rules.isEmpty(); }
  bool contains(Term* t) const;
  bool contains(Term* t, TermList& rhs);
  bool isBlocked(Term* t);
  bool blockTerm(Term* t, Term* rwTerm);
  bool addRewrite(Term* t, TermList into, Term* rwTerm);

  void copyRewriteRules(RewritingData* other)
  {
    ASS(isEmpty()); // this can be done only once

    DHMap<Term*,RuleInfo>::Iterator it(other->_rules);
    while (it.hasNext()) {
      Term* lhs;
      RuleInfo info;
      it.next(lhs,info);
      ALWAYS(addRewrite(lhs, info.rhs, nullptr/* info.rwTerm */));
    }
  }

  template<class Applicator>
  bool addRewriteRules(Clause* cl, Applicator f, Term* rwTerm = nullptr)
  {
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
  bool subsumes(RewritingData* other, Applicator f, Term* rwTerm)
  {
    TIME_TRACE("subsumes");

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
      if (rwTerm && !_ord.isGreater(TermList(rwTerm), TermList(lhs))) {
        continue;
      }
      if (!other) {
        return false;
      }
      auto ptr = other->_rules.findPtr(lhs);
      if (!ptr) {
        return false;
      }
      if (!other->validate(lhs, *ptr)) {
        other->_rules.remove(lhs);
        return false;
      }
      if (rhs.isNonEmpty()) {
        rhs = f(rhs);
      }

      if (!subsumes(rhs, ptr->rhs)) {
        return false;
      }
    }
    return true;
  }

  inline bool subsumes(TermList rhs, TermList rhsOther) {
    // other is blocked
    // return rhs == rhsOther;
    if (rhs.isEmpty() || rhsOther.isEmpty()) {
      return false;
    }

    // if (rhsOther.isEmpty()) {
    //   return true;
    // }
    // // this is blocked
    // if (rhs.isEmpty()) {
    //   return false;
    // }
    // std::cout << "comparing " << rhs << " and " << rhsOther << std::endl;
    return Ordering::isGorGEorE(_ord.compare(rhsOther,rhs));
  }

  bool blockNewBasic(Term* rwLhs, ResultSubstitution* subst, bool result);
  bool blockNewTerms(Term* rwLhs, Literal* rwLit);
  bool blockNewTerms(Clause* cl, ResultSubstitution* subst, bool eqIsResult, Term* rwLhs);
  bool validate(Term* lhs, RuleInfo& info);

  void setClause(Clause* cl) {
    _cl = cl;
  }

  size_t size() { return this->_rules.size(); }

  vstring toString() const;

  DHMap<Term*,RuleInfo>::DelIterator iter() {
    return DHMap<Term*,RuleInfo>::DelIterator(_rules);
  }

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
        if (!rwData->isBlocked(st)) {
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

