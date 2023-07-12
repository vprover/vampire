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

#include "Indexing/TermIndexingStructure.hpp"
#include "RobSubstitution.hpp"

namespace Kernel {

using namespace Indexing;

class RewritingData {
public:
  CLASS_NAME(RewritingData);
  USE_ALLOCATOR(RewritingData);

  RewritingData(Clause* cl) : _cl(cl) {}

  bool isEmpty() const { return _groundRules.isEmpty() && _nongroundRules.isEmpty(); }
  bool contains(Term* t) const;
  bool isBlocked(Term* t);
  bool blockTerm(Term* t);
  bool addRewrite(Term* t, TermList into);

  bool copy(RewritingData* res) {
    return copy(res, [](TermList t) { return t; });
  }

  template<class Applicator>
  bool copy(RewritingData* res, Applicator f)
  {
    CALL("RewritingData::copy");
    TIME_TRACE("rewritingdata-copy");

    res->_groundRules.loadFromMap(_groundRules);
    TIME_TRACE("rewritingdata-copy nonground");
    DHMap<Term*,TermList>::Iterator it(_nongroundRules);
    while (it.hasNext()) {
      Term* lhs;
      TermList rhs;
      it.next(lhs,rhs);
      if (!res->addRewrite(f(TermList(lhs)).term(), rhs.isEmpty() ? rhs : f(rhs))) {
        return false;
      }
    }
    return true;
  }

  template<class Applicator,class Filter>
  bool merge(RewritingData* other, Applicator f, Filter g)
  {
    CALL("RewritingData::merge");
    TIME_TRACE("rewritingdata-merge");

    DHMap<Term*,TermList>::Iterator git(other->_groundRules);
    while (git.hasNext()) {
      Term* lhs;
      TermList rhs;
      git.next(lhs,rhs);
      if (!g(lhs)) {
        continue;
      }
      if (!addRewrite(lhs,rhs)) {
        return false;
      }
    }

    DHMap<Term*,TermList>::Iterator ngit(other->_nongroundRules);
    while (ngit.hasNext()) {
      Term* lhs;
      TermList rhs;
      ngit.next(lhs,rhs);
      lhs = f(TermList(lhs)).term();
      if (!g(lhs)) {
        continue;
      }
      if (!addRewrite(lhs, rhs.isEmpty() ? rhs : f(rhs))) {
        return false;
      }
    }
    return true;
  }

  template<class Applicator,class Filter>
  bool subsumes(RewritingData* other, Applicator f, Filter g)
  {
    CALL("RewritingData::subsumes");
    TIME_TRACE("rewritingdata-subsumes");

    if (_groundRules.size() > other->_groundRules.size()) {
      return false;
    }
    DHMap<Term*,TermList>::Iterator git(_groundRules);
    while (git.hasNext()) {
      Term* lhs;
      TermList rhs;
      git.next(lhs,rhs);
      if (!g(lhs)) {
        continue;
      }
      auto ptr = other->_groundRules.findPtr(lhs);
      if (!ptr || !subsumes(rhs, *ptr)) {
        return false;
      }
    }
    DHMap<Term*,TermList>::Iterator ngit(_nongroundRules);
    while (ngit.hasNext()) {
      Term* lhs;
      TermList rhs;
      ngit.next(lhs,rhs);
      lhs = f(TermList(lhs)).term();
      if (!g(lhs)) {
        continue;
      }
      if (rhs.isNonEmpty()) { 
        rhs = f(rhs);
      }
      if (lhs->ground() && rhs.isTerm() && rhs.term()->ground()) {
        auto ptr = other->_groundRules.findPtr(lhs);
        if (!ptr || !subsumes(rhs, *ptr)) {
          return false;
        }
      } else {
        auto ptr = other->_nongroundRules.findPtr(lhs);
        if (!ptr || !subsumes(rhs, *ptr)) {
          return false;
        }
      }
    }
    TIME_TRACE("rewritingdata-subsumes success");
    return true;
  }

  inline bool subsumes(TermList rhs, TermList rhsOther) {
    return rhsOther.isEmpty() || rhs == rhsOther;
  }

  VirtualIterator<pair<Term*,TermList>> items() const {
    return pvi(getConcatenatedIterator(_groundRules.items(), _nongroundRules.items()));
  }

  vstring toString() const;

private:
  DHMap<Term*,TermList> _groundRules;
  DHMap<Term*,TermList> _nongroundRules;
  Clause* _cl;
  DHSet<unsigned> _vars;
  bool _varsComputed = false;
};

};

#endif /*__RewritingData__*/

