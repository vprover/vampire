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

#include "Kernel/FlatTerm.hpp"
#include "Kernel/Term.hpp"

#include "Index.hpp"

#include "TermCodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

template<class Data>
void TermCodeTree<Data>::onCodeOpDestroying(CodeOp* op)
{
  if (op->isSuccess()) {
    delete op->getSuccessResult<Data>();
  }
}

template<class Data>
TermCodeTree<Data>::TermCodeTree()
{
  _clauseCodeTree=false;
  _onCodeOpDestroying = onCodeOpDestroying;
}

template<class Data>
void TermCodeTree<Data>::insert(Data* data)
{
  static CodeStack code;
  code.reset();

  TermList t=data->term;
  if (t.isVar()) {
    code.push(CodeOp::getTermOp(ASSIGN_VAR,0));
  }
  else {
    ASS(t.isTerm());

    TermCompiler compiler(code);
    compiler.handleTerm(t.term());
    compiler.updateCodeTree(this);
  }

  code.push(CodeOp::getSuccess(data));
  incorporate(code);  
  //@b incorporate should empty the code stack
  ASS(code.isEmpty());
}

//////////////// removal ////////////////////

template<class Data>
void TermCodeTree<Data>::remove(const Data& data)
{
  static RemovingTermMatcher rtm;
  static Stack<CodeOp*> firstsInBlocks;
  firstsInBlocks.reset();

  FlatTerm* ft=FlatTerm::create(data.term);
  rtm.init(ft, this, &firstsInBlocks);
  
  Data* dptr = nullptr;
  for(;;) {
    if (!rtm.next()) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("term being removed was not found");
    }
    ASS(rtm.op->isSuccess());
    dptr=rtm.op->template getSuccessResult<Data>();
    if (*dptr==data) {
      break;
    }
  }
  
  rtm.op->makeFail();

  ASS(dptr);
  delete dptr;
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

template<class Data>
void TermCodeTree<Data>::RemovingTermMatcher::init(FlatTerm* ft_,
					     TermCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  RemovingMatcher::init(tree_->getEntryPoint(), 0, 0, tree_, firstsInBlocks_);
  
  firstsInBlocks->push(entry);

  ft=ft_;
  tp=0;
  op=entry;
}

//////////////// retrieval ////////////////////

template<class Data>
TermCodeTree<Data>::TermMatcher::TermMatcher()
{
#if VDEBUG
  ft=0;
#endif
}

template<class Data>
void TermCodeTree<Data>::TermMatcher::init(CodeTree* tree, TermList t)
{
  Matcher::init(tree,tree->getEntryPoint());

  linfos=0;
  linfoCnt=0;

  ASS(!ft);
  ft = FlatTerm::createUnexpanded(t);

  op=entry;
  tp=0;
}

template<class Data>
void TermCodeTree<Data>::TermMatcher::reset()
{
  ft->destroy();
#if VDEBUG
  ft=0;
#endif
}

template<class Data>
Data* TermCodeTree<Data>::TermMatcher::next()
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
  return op->getSuccessResult<Data>();
}

template class TermCodeTree<TermLiteralClause>;
template class TermCodeTree<DemodulatorData>;

};
