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

class FilterFn {
public:
  FilterFn() : _ord(nullptr), _t() {}
  FilterFn(Ordering* ord, TermList t) : _ord(ord), _t(t) {}

  bool operator()(Term* arg) const {
    return !_ord || _ord->compare(_t,TermList(arg))==Ordering::Result::GREATER;
  }

private:
  Ordering* _ord;
  TermList _t;
};

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

class RewritingData {
public:
  CLASS_NAME(RewritingData);
  USE_ALLOCATOR(RewritingData);

  // bool isEmpty() const { return _groundRules.isEmpty() && _nongroundRules.isEmpty(); }
  bool isEmpty() const { return _rules.isEmpty(); }
  bool contains(Term* t) const;
  bool isBlocked(Term* t);
  bool isRewritten(Term* t);
  bool blockTerm(Term* t);
  bool addRewrite(Term* t, TermList into);

  bool addRewriteRules(RewritingData* res) {
    static FilterFn filter;
    return addRewriteRules(res, [](TermList t) { return t; }, filter);
  }

  template<class Applicator>
  bool addRewriteRules(RewritingData* other, Applicator f, const FilterFn& g)
  {
    CALL("RewritingData::addRewriteRules");
    if (!other) {
      return true;
    }

    DHMap<Term*,TermList>::Iterator ngit(other->_rules);
    while (ngit.hasNext()) {
      Term* lhs;
      TermList rhs;
      ngit.next(lhs,rhs);
      lhs = f(TermList(lhs)).term();
      {
        TIME_TRACE("filter");
        if (!g(lhs)) {
          continue;
        }
      }
      if (!addRewrite(lhs, rhs.isEmpty() ? rhs : f(rhs))) {
        return false;
      }
    }
    return true;
  }

  template<class Applicator>
  bool copySubsumes(RewritingData* subsumer, RewritingData* subsumed, /* Term* rwTerm, TermList tgtTerm, */ Applicator f, const FilterFn& g, Ordering& ord)
  {
    CALL("RewritingData::copySubsumes");
    if (subsumer) {
      DHMap<Term*,TermList>::DelIterator ngit(subsumer->_rules);
      while (ngit.hasNext()) {
        Term* lhs;
        TermList rhs;
        ngit.next(lhs,rhs);
        if(!subsumer->validate(lhs, rhs, ord)) {
          ngit.del();
          continue;
        }
        lhs = f(TermList(lhs)).term();
        {
          TIME_TRACE("filter");
          if (!g(lhs)) {
            continue;
          }
        }
        if (!addRewrite(lhs, rhs.isEmpty() ? rhs : f(rhs))) {
          return false;
        }
      }
    }
    // if (!addRewrite(f(TermList(rwTerm)).term(), f(tgtTerm))) {
    //   return false;
    // }
    // NonVariableNonTypeIterator nvi(rwTerm);
    // while (nvi.hasNext()) {
    //   auto st = nvi.next();
    //   if (!blockTerm(f(TermList(st)).term())) {
    //     return false;
    //   }
    // }

    if (subsumed) {
      DHMap<Term*,TermList>::Iterator ngit2(subsumed->_rules);
      while (ngit2.hasNext()) {
        Term* lhs;
        TermList rhs;
        ngit2.next(lhs,rhs);
        addRewrite(lhs, rhs);
      }
    }
    return true;
  }

  template<class Applicator>
  bool subsumes(RewritingData* other, Applicator f, const FilterFn& g, Ordering& ord)
  {
    CALL("RewritingData::subsumes");

    DHMap<Term*,TermList>::DelIterator ngit(_rules);
    while (ngit.hasNext()) {
      Term* lhs;
      TermList rhs;
      ngit.next(lhs,rhs);
      if (!validate(lhs, rhs, ord)) {
        ngit.del();
        continue;
      }
      lhs = f(TermList(lhs)).term();
      {
        TIME_TRACE("filter");
        if (!g(lhs)) {
          continue;
        }
      }
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
        } else if (!subsumes(rhs, *ptr, ord)) {
          return false;
        }
      }
    }
    return true;
  }

  inline bool subsumes(TermList rhs, TermList rhsOther, Ordering& ord) {
    // other is blocked
    if (rhsOther.isEmpty()) {
      return true;
    }
    // this is blocked
    if (rhs.isEmpty()) {
      return false;
    }
    // if (ord) {
      return Ordering::isGorGEorE(ord.compare(rhsOther,rhs));
    // }
    // return rhs == rhsOther;
  }


  NonVariableNonTypeIterator getSubtermIterator(Literal* lit, const Ordering& ord)
  {
    CALL("getSubtermIterator");

    if (lit->isEquality()) {
      TermList sel;
      switch(ord.getEqualityArgumentOrder(lit)) {
      case Ordering::INCOMPARABLE: {
        return NonVariableNonTypeIterator(lit);
      }
      case Ordering::EQUAL:
      case Ordering::GREATER:
      case Ordering::GREATER_EQ:
        sel=*lit->nthArgument(0);
        break;
      case Ordering::LESS:
      case Ordering::LESS_EQ:
        sel=*lit->nthArgument(1);
        break;
  #if VDEBUG
      default:
        ASSERTION_VIOLATION;
  #endif
      }
      if (!sel.isTerm()) {
        return NonVariableNonTypeIterator();
      }
      return NonVariableNonTypeIterator(sel.term(), true);
    }

    return NonVariableNonTypeIterator(lit);
  }

  bool blockNewTerms(Clause* cl, ResultSubstitution* subst, bool eqIsResult, TermList rwTerm, Ordering& ord);
  bool validate(Term* lhs, TermList rhs, Ordering& ord);

  VirtualIterator<pair<Term*,TermList>> items() const {
    return _rules.items();
  }

  void setClause(Clause* cl) {
    _cl = cl;
  }

  vstring toString() const;

private:
  DHMap<Term*,TermList> _rules;
  DHSet<Term*> _ruleValid;
  Clause* _cl;
  DHSet<unsigned> _vars;
  bool _varsComputed = false;
};

};

#endif /*__RewritingData__*/

