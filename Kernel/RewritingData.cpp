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
 * @file RewritingData.cpp
 * Implements class RewritingData
 */

#include "RewritingData.hpp"

#include "Clause.hpp"
#include "TermIterators.hpp"

namespace Kernel {

bool RewritingData::rewriteTerm(Term* t, TermList into)
{
  CALL("RewritingData::rewriteTerm");
  TIME_TRACE("rewritingdata rewriteTerm");
  if (t->ground() && into.isTerm() && into.term()->ground()) {
    return _groundRules.findOrInsert(t,into) == into;
  }
  if (!_varsComputed) {
    auto vit = _cl->getVariableIterator();
    while (vit.hasNext()) {
      _vars.insert(vit.next());
    }
    _varsComputed = true;
  }
  VariableIterator vit(t);
  while (vit.hasNext()) {
    if (!_vars.find(vit.next().var())) {
      return true;
    }
  }
  if (into.isNonEmpty()) {
    vit.reset(into);
    while (vit.hasNext()) {
      if (!_vars.find(vit.next().var())) {
        return true;
      }
    }
  }
  return _nongroundRules.findOrInsert(t,into) == into;
}

// bool Clause::hasRewriteRule(TermList lhs, TermList rhs)
// {
//   TIME_TRACE("has rewrite rule");
//   if (lhs.isVar()) {
//     return true;
//   }
//   auto ptr = _rewriteRules.findPtr(lhs);
//   return ptr && *ptr == rhs;
// }

bool RewritingData::blockTerm(Term* t)
{
  TermList empty;
  empty.makeEmpty();
  return rewriteTerm(t, empty);
}

bool RewritingData::contains(Term* t) const
{
  return _groundRules.find(t) || _nongroundRules.find(t);
}

vstring RewritingData::toString() const
{
  vstring res;
  auto it = items();
  while (it.hasNext()) {
    auto kv = it.next();
    if (kv.second.isEmpty()) {
      res += "!" + kv.first->toString();
    } else {
      res += kv.first->toString() + " -> " + kv.second.toString();
    }
    if (it.hasNext()) {
      res += ", ";
    }
  }
  return res;
}

}
