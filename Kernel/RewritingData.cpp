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
  TIME_TRACE("add rewrite");

// #if VDEBUG
//   if (into.isNonEmpty()) {
//     NonVariableNonTypeIterator nvi(t);
//     while (nvi.hasNext()) {
//       auto st = nvi.next();
//       auto ptr = _rules.findPtr(st);
//       ASS(!ptr || ptr->isEmpty());
//     }
//   }
// #endif

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
  return ptr && ptr->isEmpty();
}

bool RewritingData::isRewritten(Term* t)
{
  auto ptr = _rules.findPtr(t);
  return ptr && ptr->isNonEmpty();
}

bool RewritingData::blockNewTerms(Clause* cl, ResultSubstitution* subst, bool result, TermList rwTerm, Ordering& ord) {
  DHSet<Term*> added;
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    auto lit = subst->apply((*cl)[i], result);
    // auto tit = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit, ord)
    //                                          : EqHelper::getSubtermIterator(lit, ord);
    auto tit = getSubtermIterator(lit, ord);
    while (tit.hasNext()) {
      auto st = tit.next();
      if (added.find(st)) {
        tit.right();
        continue;
      }
      added.insert(st);
      {
        TIME_TRACE("filter");
        auto comp = ord.compare(rwTerm,TermList(st));
        if (Ordering::isGorGEorE(comp)) {
          // add the term itself as well if GREATER
          NonVariableNonTypeIterator inner(st,comp==Ordering::GREATER);
          while (inner.hasNext()) {
            auto st = inner.next();
            if (added.find(st)) {
              inner.right();
              continue;
            }
            added.insert(st);
            if (!blockTerm(st)) {
              return false;
            }
          }
        }
      }
      // if (!blockTerm(st)) {
      //   return false;
      // }
    }
  }
  return true;
}

bool RewritingData::varCheck(Term* lhs, TermList rhs)
{
  CALL("RewritingData::varCheck");
  TIME_TRACE("variable computation");
  if (_ruleValid.find(lhs)) {
    return true;
  }
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
  _ruleValid.insert(lhs);
  return true;
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
