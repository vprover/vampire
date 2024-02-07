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

using namespace std;

namespace Kernel {

bool RewritingData::addRewrite(Term* t, TermList into, Term* rwTerm)
{
  ASS(!rwTerm || _ord.isGreater(TermList(rwTerm),TermList(t)) || ((Term*)nullptr)->isLiteral());
  RuleInfo info;
  info.rhs = into;
  // info.rwTerm = rwTerm;
  ASS(into.isEmpty() || !rwTerm || t==rwTerm);
  ASS(_cl);

  if (!validate(t, info)) {
    return true;
  }

  // try insertion
  RuleInfo* ptr;
  if (_rules.getValuePtr(t, ptr, info)) {
    return true;
  }

  // check if rhs's agree
  // ASS(ptr->valid);
  // ASS(!ptr->rwTerm || ptr->rwTerm == rwTerm);
  // if (into == ptr->rhs) {
  //   return true;
  // }

  // // otherwise see if t really needs to be inserted
  // return !_ord.isGreater(TermList(t),TermList(rwTerm));
  return into == ptr->rhs;
}

bool RewritingData::blockTerm(Term* t, Term* rwTerm)
{
  ASS(_cl);
  TermList empty;
  empty.makeEmpty();
  return addRewrite(t, empty, rwTerm);
}

bool RewritingData::contains(Term* t) const
{
  return _rules.find(t);
}

bool RewritingData::contains(Term* t, TermList& rhs)
{
  auto ptr = _rules.findPtr(t);
  if (!ptr) {
    return false;
  }
  if (!validate(t,*ptr)) {
    _rules.remove(t);
    return false;
  }
  rhs = ptr->rhs;
  return true;
}

bool RewritingData::isBlocked(Term* t)
{
  auto ptr = _rules.findPtr(t);
  if (!ptr) {
    return false;
  }
  if (!validate(t,*ptr)) {
    _rules.remove(t);
    return false;
  }
  return ptr->rhs.isEmpty();
}

template<class SubtermIterator>
SubtermIterator getSubtermIterator(Literal* lit, const Ordering& ord)
{
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

bool RewritingData::blockNewBasic(Term* rwLhs, ResultSubstitution* subst, bool result)
{
  DHSet<unsigned> vars;
  DHSet<Term*> done;
  VariableIterator vit(rwLhs);
  while (vit.hasNext()) {
    auto v = vit.next();
    if (!vars.insert(v.var())) {
      continue;
    }
    auto st = subst->applyTo(v,result);
    if (st.isVar()) {
      continue;
    }
    NonVariableNonTypeIterator nvi(st.term(), true);
     while (nvi.hasNext()) {
      auto st = nvi.next();
      if (!done.insert(st)) {
        nvi.right();
        continue;
      }
      if (!blockTerm(st, nullptr)) {
        return false;
      }
    }
  }
  return true;
}

bool RewritingData::blockNewTerms(Term* rwTerm, Literal* rwLit)
{
  DHSet<Term*> done;
  auto tit = getSubtermIterator<NonVariableNonTypeIterator>(rwLit, _ord);
  while (tit.hasNext()) {
    auto st = tit.next();
    if (st != rwTerm && !done.insert(st)) {
      tit.right();
      continue;
    }
    // if (!_ord.isGreater(TermList(rwTerm), TermList(st))) {
    //   continue;
    // }
    if (!_ord.isGreater(TermList(st), TermList(rwTerm))) {
      continue;
    }
    if (!blockTerm(st, rwTerm)) {
      return false;
    }
  }
  // NonVariableNonTypeIterator nvi(rwTerm, false);
  // while (nvi.hasNext()) {
  //   auto st = nvi.next();
  //   if (!done.insert(st)) {
  //     nvi.right();
  //     continue;
  //   }
  //   if (!blockTerm(st, rwTerm)) {
  //     return false;
  //   }
  // }
  return true;
}

bool RewritingData::blockNewTerms(Clause* cl, ResultSubstitution* subst, bool result, Term* rwTerm)
{
  DHSet<Term*> done;
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
      if (!blockTerm(st, rwTerm)) {
        return false;
      }
    }
  }
  return true;
}

bool RewritingData::validate(Term* lhs, RuleInfo& info)
{
  TIME_TRACE("validate");
  if (info.valid) {
    return true;
  }

//   bool anyContains = iterTraits(_cl->iterLits())
//     .any([lhs](Literal* lit) {
//       if (lit->isEquality()) {
//         if (lit->nthArgument(0)->containsSubterm(TermList(lhs)) && *lit->nthArgument(0)!=TermList(lhs)) {
//           return true;
//         }
//         if (lit->nthArgument(1)->containsSubterm(TermList(lhs)) && *lit->nthArgument(1)!=TermList(lhs)) {
//           return true;
//         }
//         return false;
//       }
//       return lit->containsSubterm(TermList(lhs));
//     });

//   if (anyContains) {
//     info.valid = true;
//     return true;
//   }
//   return false;

// /////

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
  if (info.rhs.isNonEmpty()) {
    vit.reset(info.rhs);
    while (vit.hasNext()) {
      if (!_vars.find(vit.next().var())) {
        return false;
      }
    }
  }

  // check if the rule lhs is bigger than all maximal terms
  // bool greater = true;
  bool smaller = false;
  if (!_maximalLits) {
    for (unsigned i = 0; i < _cl->length(); i++) {
      LiteralList::push((*_cl)[i],_maximalLits);
    }
    _ord.removeNonMaximal(_maximalLits);
  }
  auto lits = _maximalLits;
  while (lits) {
    auto lit = lits->head();
    lits = lits->tail();
    for (unsigned j = 0; j < lit->numTermArguments(); j++) {
      auto arg = lit->termArg(j);
      // auto comp = _ord.compare(TermList(lhs),arg);
      // if (comp != Ordering::GREATER/*  && comp != Ordering::Result::EQUAL */) {
      // if (!_ord.isGreater(TermList(lhs),arg)) {
      //   greater = false;
      //   break;
      // }
      if (_ord.isGreater(arg,TermList(lhs))) {
        smaller = true;
        break;
      }
    }
    // if (!greater) {
    //   break;
    // }
    if (smaller) {
      break;
    }
  }
  // if (greater) {
  //   return false;
  // }
  if (!smaller) {
    return false;
  }

  // finally, check if the rule lhs is not greater than the
  // lhs of the associated rewrite (where it was copied from)
  // if (info.rwTerm && info.rhs.isEmpty()) {
  //   if (!_ord.isGreater(TermList(info.rwTerm),TermList(lhs))) {
  //     return false;
  //   }
  // }
  // info.rwTerm = nullptr;
  info.valid = true;
  NonVariableNonTypeIterator nvi(lhs);
  while(nvi.hasNext()) {
    auto st = nvi.next();
    auto ptr = _rules.findPtr(st);
    if (!ptr) {
      continue;
    }
    if (ptr->valid) {
      nvi.right();
      continue;
    }
    // ptr->rwTerm = nullptr;
    ptr->valid = true;
  }
  return true;
}

vstring RewritingData::toString() const
{
  vstring res;
  auto it = _rules.items();
  while (it.hasNext()) {
    auto kv = it.next();
    // if (kv.second.valid) {
    //   res += "!";
    // } else {
    //   res += "?";
    // }
    if (kv.second.rhs.isEmpty()) {
      res += "~" + kv.first->toString();
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
