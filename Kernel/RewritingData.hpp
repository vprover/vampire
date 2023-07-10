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
  bool rewriteTerm(Term* t, TermList into, TermList origLhs, Literal* lit, Clause* cl);

  // using Applicator = std::function<TermList(TermList)>;
  // using Filter = std::function<bool(Term*)>;

  template<class Applicator>
  bool copy(RewritingData* res, Applicator f)
  {
    CALL("RewritingData::copy");
    TIME_TRACE("rewritingdata-copy");

    res->_groundRules.loadFromMap(_groundRules);
    TIME_TRACE("rewritingdata-copy nonground");
    DHMap<Term*,pair<TermList,TermQueryResult>>::Iterator it(_nongroundRules);
    while (it.hasNext()) {
      Term* lhs;
      auto& kv = it.nextRef(lhs);
      if (!res->addEntry(
        f(TermList(lhs)).term(),
        kv.first.isEmpty() ? kv.first : f(kv.first),
        kv.second
      )) {
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

    DHMap<Term*,pair<TermList,TermQueryResult>>::Iterator git(other->_groundRules);
    while (git.hasNext()) {
      Term* lhs;
      auto& kv = git.nextRef(lhs);
      if (!g(lhs)) {
        continue;
      }
      if (!addEntry(lhs,kv.first,kv.second)) {
        return false;
      }
    }

    DHMap<Term*,pair<TermList,TermQueryResult>>::Iterator ngit(other->_nongroundRules);
    while (ngit.hasNext()) {
      Term* lhs;
      auto& kv = ngit.nextRef(lhs);
      lhs = f(TermList(lhs)).term();
      if (!g(lhs)) {
        continue;
      }
      if (!addEntry(lhs, kv.first.isEmpty() ? kv.first : f(kv.first), kv.second))
      {
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
    DHMap<Term*,pair<TermList,TermQueryResult>>::Iterator git(_groundRules);
    while (git.hasNext()) {
      Term* lhs;
      auto& kv = git.nextRef(lhs);
      if (!g(lhs)) {
        continue;
      }
      auto ptr = other->_groundRules.findPtr(lhs);
      if (!ptr || ptr->first != kv.first) {
        return false;
      }
    }
    DHMap<Term*,pair<TermList,TermQueryResult>>::Iterator ngit(_nongroundRules);
    while (ngit.hasNext()) {
      Term* lhs;
      auto& kv = ngit.nextRef(lhs);
      lhs = f(TermList(lhs)).term();
      if (!g(lhs)) {
        continue;
      }
      auto rhs = kv.first.isEmpty() ? kv.first : f(kv.first);
      if (lhs->ground() && rhs.isTerm() && rhs.term()->ground()) {
        auto ptr = other->_groundRules.findPtr(lhs);
        if (!ptr || ptr->first != rhs) {
          return false;
        }
      } else {
        auto ptr = other->_nongroundRules.findPtr(lhs);
        if (!ptr || ptr->first != rhs) {
          return false;
        }
      }
    }
    TIME_TRACE("rewritingdata-subsumes success");
    return true;
  }

  VirtualIterator<pair<Term*,pair<TermList,TermQueryResult>>> items() const {
    return pvi(getConcatenatedIterator(_groundRules.items(), _nongroundRules.items()));
  }

  vstring toString() const;

private:
  bool addEntry(Term* t, TermList into, TermQueryResult qr);

  DHMap<Term*,pair<TermList,TermQueryResult>> _groundRules;
  DHMap<Term*,pair<TermList,TermQueryResult>> _nongroundRules;
  Clause* _cl;
  DHSet<unsigned> _vars;
  bool _varsComputed = false;
};

};

#endif /*__RewritingData__*/

