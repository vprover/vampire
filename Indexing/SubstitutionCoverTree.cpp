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

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"

#include "ResultSubstitution.hpp"

namespace Indexing
{

SubstitutionCoverTree::SubstitutionCoverTree(Clause* cl)
: _varSorts()//, _tis()
{
  _clauseCodeTree=false;
  for (unsigned i = 0; i < cl->length(); i++) {
    SortHelper::collectVariableSorts((*cl)[i], _varSorts);
  }
  // bool added;
  // vstring fnname = "sFN_varwrap_";
  // DHMap<unsigned,TermList>::Iterator vit(_varSorts);
  // while (vit.hasNext()) {
  //   unsigned v;
  //   TermList t;
  //   vit.next(v,t);
  //   // cannot handle type vars yet
  //   if (t==AtomicSort::superSort()) {
  //     _varSorts.reset();
  //     break;
  //   }
  //   fnname += t.toString();
  // }
  // if (_varSorts.isEmpty()) {
  //   return;
  // }
  // _fn = env.signature->addFunction(fnname,_varSorts.size(),added);
  // if (added) {
  //   DHMap<unsigned,TermList>::Iterator vit(_varSorts);
  //   TermStack args;
  //   while (vit.hasNext()) {
  //     args.push(vit.next());
  //   }
  //   auto ot = OperatorType::getFunctionType(args.size(), args.begin(), args[0]);
  //   env.signature->getFunction(_fn)->setType(ot);
  // }
}

bool SubstitutionCoverTree::checkAndInsert(ResultSubstitution* subst, bool result, bool doInsert)
{
  if (_varSorts.isEmpty()) {
    return true;
  }
  DHMap<unsigned,TermList>::Iterator vit(_varSorts);
  TermStack ts;
  while (vit.hasNext()) {
    auto v = vit.nextKey();
    ts.push(subst->apply(TermList(v,false), result));
  }
  // TermList t(Term::create(_fn, args.size(), args.begin()));
  // auto oldCheck = _tis.generalizationExists(t);
  auto newCheck = check(ts);
  // if (oldCheck != newCheck) {
  //   USER_ERROR("checks don't match");
  // }
  if (newCheck) {
    return false;
  }
  if (doInsert) {
    insert(ts,this);
    // _tis.insert(t.term(), nullptr, nullptr);
  }
  return true;
}

void SubstitutionCoverTree::insert(const TermStack& ts, void* ptr)
{
  static CodeStack code;
  code.reset();

  static CompileContext cctx;
  cctx.init();
  for (const auto& t : ts) {
    if (t.isVar()) {
      unsigned var=t.var();
      unsigned* varNumPtr;
      if (cctx.varMap.getValuePtr(var,varNumPtr)) {
        *varNumPtr=cctx.nextVarNum++;
        code.push(CodeOp::getTermOp(ASSIGN_VAR, *varNumPtr));
      }	else {
        code.push(CodeOp::getTermOp(CHECK_VAR, *varNumPtr));
      }
    }
    else {
      ASS(t.isTerm());
      compileTerm(t.term(), code, cctx, false);
    }
  }
  cctx.deinit(this);

  // just put anything non-null in there to get a valid success
  code.push(CodeOp::getSuccess(ptr));
  incorporate(code);
}

bool SubstitutionCoverTree::check(const TermStack& ts)
{
  if (isEmpty()) {
    return false;
  }

  static SubstMatcher matcher;

  matcher.init(this, ts);
  bool res = matcher.next();
  matcher.reset();

  return res;
}

void SubstitutionCoverTree::SubstMatcher::init(CodeTree* tree, const TermStack& ts)
{
  Matcher::init(tree,tree->getEntryPoint());

  linfos=0;
  linfoCnt=0;

  ft=FlatTerm::create(ts);

  op=entry;
  tp=0;
}

void SubstitutionCoverTree::SubstMatcher::reset()
{
  ft->destroy();
}

void* SubstitutionCoverTree::SubstMatcher::next()
{
  if (finished()) {
    //all possible matches are exhausted
    return 0;
  }

  _matched=execute();
  if (!_matched) {
    return 0;
  }

  ASS(op->isSuccess());
  return op->getSuccessResult();
}

}
