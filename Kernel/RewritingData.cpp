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

bool RewritingData::addRewrite(Term* t, TermList into, Term* rwTerm)
{
  CALL("RewritingData::addRewrite");
  RuleInfo info;
  info.rhs = into;
  info.rwTerm = rwTerm;

  // try insertion
  RuleInfo* ptr;
  if (_rules.getValuePtr(t, ptr, info)) {
    return true;
  }

  // check if rhs's agree
  // ASS(ptr->valid);
  ASS(!ptr->rwTerm || ptr->rwTerm == rwTerm);
  if (into == ptr->rhs) {
    return true;
  }

  // otherwise see if t really needs to be inserted
  TIME_TRACE("condition precheck");
  return (_ord.compare(TermList(rwTerm),TermList(t)) != Ordering::Result::GREATER);
}

bool RewritingData::blockTerm(Term* t, Term* rwTerm)
{
  CALL("RewritingData::blockTerm");
  TermList empty;
  empty.makeEmpty();
  return addRewrite(t, empty, rwTerm);
}

bool RewritingData::contains(Term* t) const
{
  CALL("RewritingData::contains");
  return _rules.find(t);
}

bool RewritingData::isBlocked(Term* t)
{
  CALL("RewritingData::isBlocked");
  auto ptr = _rules.findPtr(t);
  ASS(!ptr || ptr->valid);
  return ptr && ptr->rhs.isEmpty();
}

bool RewritingData::isBlockedUnsafe(Term* t)
{
  CALL("RewritingData::isBlockedUnsafe");
  auto ptr = _rules.findPtr(t);
  return ptr && ptr->rhs.isEmpty();
}

bool RewritingData::isRewritten(Term* t)
{
  auto ptr = _rules.findPtr(t);
  ASS(!ptr || ptr->valid);
  return ptr && ptr->rhs.isNonEmpty();
}

template<class SubtermIterator>
SubtermIterator getSubtermIterator(Literal* lit, const Ordering& ord)
{
  CALL("getSubtermIterator");

  if (lit->isEquality()) {
    TermList sel;
    switch(ord.getEqualityArgumentOrder(lit)) {
    case Ordering::INCOMPARABLE: {
      return SubtermIterator(lit);
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
      return SubtermIterator();
    }
    return SubtermIterator(sel.term(), true);
  }

  return SubtermIterator(lit);
}

bool RewritingData::blockNewTerms(Clause* cl, ResultSubstitution* subst, bool result, Term* rwTerm)
{
  CALL("RewritingData::blockNewTerms");
  DHSet<Term*> done;
  // if (rwTerm) {
  //   done.insert(rwTerm);
  // }
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    auto lit = subst->apply((*cl)[i], result);
    auto tit = /* env.options->combinatorySup() ? getSubtermIterator<FirstOrderSubtermIt>(lit, ord)
                                             :  */getSubtermIterator<NonVariableNonTypeIterator>(lit, _ord);
    while (tit.hasNext()) {
      auto st = tit.next();
      if (st != rwTerm && !done.insert(st)) {
        tit.right();
        continue;
      }
      TIME_TRACE("filter-block");
      if (!blockTerm(st, rwTerm)) {
        return false;
      }
    }
  }
  return true;
}

bool RewritingData::validate(Term* lhs)
{
  CALL("RewritingData::validate");
  TIME_TRACE("validate");
  auto ptr = _rules.findPtr(lhs);
  if (ptr->valid) {
    return true;
  }

  // check if the rule contains any variables not in the clause
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
  if (ptr->rhs.isNonEmpty()) {
    vit.reset(ptr->rhs);
    while (vit.hasNext()) {
      if (!_vars.find(vit.next().var())) {
        return false;
      }
    }
  }

  // check if the rule lhs is bigger than all maximal terms
  bool greater = true;
  LiteralList* sel=0;
  for (unsigned i = 0; i < _cl->length(); i++) {
    LiteralList::push((*_cl)[i],sel);
  }
  _ord.removeNonMaximal(sel);
  while (sel) {
    auto lit = sel->head();
    sel = sel->tail();
    for (unsigned j = 0; j < lit->arity(); j++) {
      auto arg = *lit->nthArgument(j);
      if (_ord.compare(TermList(lhs),arg)!=Ordering::GREATER) {
        greater = false;
        break;
      }
    }
    if (!greater) {
      break;
    }
  }
  if (greater) {
    return false;
  }

  // finally, check if the rule lhs is not greater than the
  // lhs of the associated rewrite (where it was copied from)
  if (ptr->rwTerm) {
    if (_ord.compare(TermList(ptr->rwTerm),TermList(lhs))!=Ordering::GREATER) {
      return false;
    }
  }
  ptr->rwTerm = nullptr;
  ptr->valid = true;
  return true;
}

void RewritingData::validate()
{
  if (_valid) {
    return;
  }
  DHMap<Term*,RuleInfo>::DelIterator it(_rules);
  while (it.hasNext()) {
    auto lhs = it.nextKey();
    if (!validate(lhs)) {
      it.del();
    }
  }
  _valid = true;
}

vstring RewritingData::toString() const
{
  vstring res;
  auto it = _rules.items();
  while (it.hasNext()) {
    auto kv = it.next();
    if (kv.second.rhs.isEmpty()) {
      res += "!" + kv.first->toString();
    } else {
      res += kv.first->toString() + " -> " + kv.second.rhs.toString();
    }
    if (it.hasNext()) {
      res += ", ";
    }
  }
  return res;
}

}
