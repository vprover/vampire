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

bool RewritingData::addRewrite(Term* t, TermList into)
{
  CALL("RewritingData::addRewrite");

  if (into.isNonEmpty()) {
    NonVariableNonTypeIterator nvi(t);
    while (nvi.hasNext()) {
      auto st = nvi.next();
      auto ptr = _rules.findPtr(st);
      if (ptr && ptr->isNonEmpty()) {
        return false;
      }
    }
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
  // if (ord) {
  //   bool greater = true;
  //   for (unsigned i = 0; i < _cl->length(); i++) {
  //     auto lit = (*_cl)[i];
  //     for (unsigned j = 0; j < lit->arity(); j++) {
  //       auto arg = lit->termArg(j);
  //       if (ord->compare(TermList(t),arg)!=Ordering::GREATER) {
  //         greater = false;
  //         break;
  //       }
  //     }
  //     if (!greater) {break;}
  //   }
  //   if (greater) {
  //     TIME_TRACE("greater than all");
  //     return true;
  //   }
  // }
  return _rules.findOrInsert(t,into) == into;
}

bool RewritingData::blockTerm(Term* t)
{
  TermList empty;
  empty.makeEmpty();
  return addRewrite(t, empty);
}

bool RewritingData::contains(Term* t) const
{
  return _rules.find(t);
}

bool RewritingData::isBlocked(Term* t)
{
  auto ptr = _rules.findPtr(t);
  if (ptr && ptr->isEmpty()) {
    return true;
  }
  return false;
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
