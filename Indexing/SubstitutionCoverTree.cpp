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
 * @file SubstitutionCoverTree.cpp
 * Implements class SubstitutionCoverTree.
 */

#include "SubstitutionCoverTree.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing
{

SubstitutionCoverTree::SubstitutionCoverTree(Clause* cl)
 : _varSorts(), _tis()
{
  for (unsigned i = 0; i < cl->length(); i++) {
    SortHelper::collectVariableSorts((*cl)[i], _varSorts);
  }
  bool added;
  vstring fnname = "sFN_varwrap_";
  DHMap<unsigned,TermList>::Iterator vit(_varSorts);
  while (vit.hasNext()) {
    unsigned v;
    TermList t;
    vit.next(v,t);
    // cannot handle type vars yet
    if (t==AtomicSort::superSort()) {
      _varSorts.reset();
      break;
    }
    fnname += t.toString();
  }
  if (_varSorts.isEmpty()) {
    return;
  }
  _fn = env.signature->addFunction(fnname,_varSorts.size(),added);
  if (added) {
    DHMap<unsigned,TermList>::Iterator vit(_varSorts);
    TermStack args;
    while (vit.hasNext()) {
      args.push(vit.next());
    }
    auto ot = OperatorType::getFunctionType(args.size(), args.begin(), args[0]);
    env.signature->getFunction(_fn)->setType(ot);
  }
}

bool SubstitutionCoverTree::checkAndInsert(ResultSubstitution* subst, bool result, bool doInsert)
{
  if (_varSorts.isEmpty()) {
    return true;
  }
  DHMap<unsigned,TermList>::Iterator vit(_varSorts);
  TermStack args;
  while (vit.hasNext()) {
    auto v = vit.nextKey();
    auto t = subst->apply(TermList(v,false), result);
    args.push(t);
  }
  TermList t(Term::create(_fn, args.size(), args.begin()));
  if (_tis.generalizationExists(t)) {
    return false;
  }
  if (doInsert) {
    _tis.insert(t.term(), nullptr, nullptr);
  }
  return true;
}

}
