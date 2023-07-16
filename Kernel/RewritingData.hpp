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

class RewritingData {
public:
  CLASS_NAME(RewritingData);
  USE_ALLOCATOR(RewritingData);

  RewritingData(Clause* cl) : _cl(cl) {}

  // bool isEmpty() const { return _groundRules.isEmpty() && _nongroundRules.isEmpty(); }
  bool isEmpty() const { return _rules.isEmpty(); }
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

    DHMap<Term*,TermList>::Iterator it(_rules);
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

  template<class Applicator>
  bool merge(RewritingData* other, Applicator f, FilterFn g)
  {
    CALL("RewritingData::merge");

    DHMap<Term*,TermList>::Iterator ngit(other->_rules);
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

  template<class Applicator>
  bool subsumes(RewritingData* other, Applicator f, FilterFn g)
  {
    CALL("RewritingData::subsumes");
    DHMap<Term*,TermList>::Iterator ngit(_rules);
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
      auto ptr = other->_rules.findPtr(lhs);
      if (!ptr || !subsumes(rhs, *ptr)) {
        return false;
      }
    }
    return true;
  }

  template<class Applicator>
  bool subsumesLiberal(RewritingData* other, Applicator f, FilterFn g)
  {
    CALL("RewritingData::subsumesLiberal");

    DHMap<Term*,TermList>::Iterator ngit(_rules);
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
      auto ptr = other->_rules.findPtr(lhs);
      if (!ptr) {
        if (rhs.isEmpty()) {
          return false;
        }
      } else if (!subsumes(*ptr, rhs)) {
        return false;
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
    return rhs == rhsOther;
  }

  VirtualIterator<pair<Term*,TermList>> items() const {
    return _rules.items();
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

