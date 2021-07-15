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
 * @file TermCodeTree.cpp
 * Implements class TermCodeTree.
 */

#include <utility>
 
#include "Lib/BitUtils.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Sort.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FlatTerm.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "TermCodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

void TermCodeTree::onCodeOpDestroying(CodeOp* op)
{
  CALL("TermCodeTree::onCodeOpDestroying");
  
  if (op->isSuccess()) {    
    delete static_cast<TermInfo*>(op->getSuccessResult());
  }
}

TermCodeTree::TermCodeTree()
{
  _clauseCodeTree=false;
  _onCodeOpDestroying = onCodeOpDestroying;
}

void TermCodeTree::insert(TermInfo* ti)
{
  CALL("TermCodeTree::insert");
  
  static CodeStack code;
  code.reset();


  TermList t=ti->t;
  if (t.isVar()) {
    code.push(CodeOp::getTermOp(ASSIGN_VAR,0));
  }
  else {
    ASS(t.isTerm());
    
    static CompileContext cctx;
    cctx.init();
    compileTerm(t.term(), code, cctx, false);
    cctx.deinit(this);
  }

  code.push(CodeOp::getSuccess(ti));
  incorporate(code);  
  //@b incorporate should empty the code stack
  ASS(code.isEmpty());
}

//////////////// removal ////////////////////

void TermCodeTree::remove(const TermInfo& ti)
{
  CALL("TermCodeTree::remove");
  
  static RemovingTermMatcher rtm;
  static Stack<CodeOp*> firstsInBlocks;
  firstsInBlocks.reset();
  
  FlatTerm* ft=FlatTerm::create(ti.t);
  rtm.init(ft, this, &firstsInBlocks);
  
  TermInfo* rti;
  for(;;) {
    if (!rtm.next()) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("term being removed was not found");
    }
    ASS(rtm.op->isSuccess());
    rti=static_cast<TermInfo*>(rtm.op->getSuccessResult());
    if (*rti==ti) {
      break;
    }
  }
  
  rtm.op->makeFail();
  
  delete rti;
  ft->destroy();
  
  optimizeMemoryAfterRemoval(&firstsInBlocks, rtm.op);
  /*
  
  static TermMatcher tm;

  tm.init(this, ti.t);

  for(;;) {
    TermInfo* found=tm.next();
    if (!found) {
      INVALID_OPERATION("term being removed was not found");
    }
    if (*found==ti) {
      tm.op->makeFail();
      delete found;
      break;
    }
  }

  tm.deinit();
  */
} // TermCodeTree::remove

void TermCodeTree::RemovingTermMatcher::init(FlatTerm* ft_, 
					     TermCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  CALL("TermCodeTree::RemovingTermMatcher::init");
  
  RemovingMatcher::init(tree_->getEntryPoint(), 0, 0, tree_, firstsInBlocks_);
  
  firstsInBlocks->push(entry);

  ft=ft_;
  tp=0;
  op=entry;
}

//////////////// retrieval ////////////////////

TermCodeTree::TermMatcher::TermMatcher()
{
#if VDEBUG
  ft=0;
#endif
}

void TermCodeTree::TermMatcher::init(CodeTree* tree, TermList t)
{
  CALL("TermCodeTree::TermMatcher::init");
  
  Matcher::init(tree,tree->getEntryPoint());

  linfos=0;
  linfoCnt=0;

  ASS(!ft);
  ft=FlatTerm::create(t);

  op=entry;
  tp=0;
}

void TermCodeTree::TermMatcher::deinit()
{
  CALL("TermCodeTree::TermMatcher::deinit");
  
  ft->destroy();
#if VDEBUG
  ft=0;
#endif
}

TermCodeTree::TermInfo* TermCodeTree::TermMatcher::next()
{
  CALL("TermCodeTree::TermMatcher::next");
  
  if (finished()) {
    //all possible matches are exhausted
    return 0;
  }
  
  _matched=execute();
  if (!_matched) {
    return 0;
  }

  ASS(op->isSuccess());
  return static_cast<TermInfo*>(op->getSuccessResult());
}

};
