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

  bool operator()(Term* arg) {
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
    return addRewriteRules(res, [](TermList t) { return t; }, FilterFn());
  }

  template<class Applicator>
  bool addRewriteRules(RewritingData* other, Applicator f, FilterFn g)
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
  bool copySubsumes(RewritingData* subsumer, RewritingData* subsumed, Term* rwTerm, TermList tgtTerm, Applicator f, FilterFn g)
  {
    CALL("RewritingData::copySubsumes");
    if (subsumer) {
      DHMap<Term*,TermList>::DelIterator ngit(subsumer->_rules);
      while (ngit.hasNext()) {
        Term* lhs;
        TermList rhs;
        ngit.next(lhs,rhs);
        if (!subsumer->varCheck(lhs, rhs)) {
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
    if (!addRewrite(rwTerm, tgtTerm)) {
      return false;
    }
    NonVariableNonTypeIterator nvi(rwTerm);
    while (nvi.hasNext()) {
      auto st = nvi.next();
      if (!blockTerm(st)) {
        return false;
      }
    }

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
  bool subsumes(RewritingData* other, Applicator f, FilterFn g, Ordering* ord)
  {
    CALL("RewritingData::subsumes");

    DHMap<Term*,TermList>::DelIterator ngit(_rules);
    while (ngit.hasNext()) {
      Term* lhs;
      TermList rhs;
      ngit.next(lhs,rhs);
      if (!varCheck(lhs, rhs)) {
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
          // return false;
          if (rhs.isEmpty()) {
            return false;
          }
        } else if (!subsumes(*ptr, rhs, ord)) {
          return false;
        }
      }
    }
    return true;
  }

  inline bool subsumes(TermList rhs, TermList rhsOther, Ordering* ord = nullptr) {
    // other is blocked
    if (rhsOther.isEmpty()) {
      return true;
    }
    // this is blocked
    if (rhs.isEmpty()) {
      return false;
    }
    if (ord) {
      return Ordering::isGorGEorE(ord->compare(rhsOther,rhs));
    }
    return rhs == rhsOther;
  }

  template<class Applicator>
  bool blockNewTerms(Clause* cl, Applicator f, FilterFn g, Ordering& ord) {
    for (unsigned i = 0; i < cl->numSelected(); i++) {
      auto lit = f((*cl)[i]);
      auto tit = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, ord)
                                               : EqHelper::getSubtermIterator(lit, ord);
      while (tit.hasNext()) {
        auto st = tit.next();
        if (!g(st)) {
          continue;
        }
        if (!blockTerm(st)) {
          return false;
        }
      }
    }
    return true;
  }

  bool varCheck(Term* lhs, TermList rhs)
  {
    CALL("RewritingData::varCheck");
    TIME_TRACE("variable computation");
    if (!_varsComputed) {
      ASS(_cl);
      auto vit = _cl->getVariableIterator();
      while (vit.hasNext()) {
        _vars.insert(vit.next());
      }
      _varsComputed = true;
    }
    VariableIterator vit(lhs);
    while (vit.hasNext()) {
      if (!_vars.find(vit.next().var())) {
        return false;
      }
    }
    if (rhs.isNonEmpty()) {
      vit.reset(rhs);
      while (vit.hasNext()) {
        if (!_vars.find(vit.next().var())) {
          return false;
        }
      }
    }
    return true;
  }

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

