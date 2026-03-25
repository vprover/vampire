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

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::onCodeOpDestroying(CodeOp* op)
{
  if (op->isSuccess()) {
    delete op->getSuccessResult<Data>();
  }
}

template<bool higherOrder, class Data>
TermCodeTree<higherOrder, Data>::TermCodeTree()
{
  _clauseCodeTree=false;
  _onCodeOpDestroying = onCodeOpDestroying;
}

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::insert(Data* data)
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

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::remove(const Data& data)
{
  static RemovingTermMatcher rtm;
  static Stack<CodeOp*> firstsInBlocks;
  firstsInBlocks.reset();

  FlatTerm* ft=FlatTerm::create(data.term);
  rtm.init(ft, this, &firstsInBlocks);
  
  Data* dptr = nullptr;
  for(;;) {
    if (!rtm.execute()) {
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

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::RemovingTermMatcher::init(FlatTerm* ft_,
					     TermCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  Base::init(tree_, tree_->getEntryPoint(), /*linfos_=*/0, /*linfoCnt_=*/0, firstsInBlocks_);
  
  Base::firstsInBlocks->push(Base::entry);

  Base::ft=ft_;
  Base::tp=0;
  Base::op=Base::entry;
}

//////////////// retrieval ////////////////////

template<bool higherOrder, class Data>
TermCodeTree<higherOrder, Data>::TermMatcher::TermMatcher()
{
#if VDEBUG
  ft=0;
#endif
}

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::TermMatcher::init(CodeTree* tree, TermList t)
{
  Base::init(tree,tree->getEntryPoint(),/*linfos_=*/0,/*linfoCnt_=*/0);

  ASS(!ft);
  ft = FlatTerm::createUnexpanded(t);

  Base::op=Base::entry;
  Base::tp=0;
}

template<bool higherOrder, class Data>
void TermCodeTree<higherOrder, Data>::TermMatcher::reset()
{
  ft->destroy();
#if VDEBUG
  ft=0;
#endif
}

template<bool higherOrder, class Data>
Data* TermCodeTree<higherOrder, Data>::TermMatcher::next()
{
  if (Base::finished()) {
    //all possible matches are exhausted
    return 0;
  }
  
  Base::_matched=Base::execute();
  if (!Base::_matched) {
    return 0;
  }

  ASS(Base::op->isSuccess());
  return Base::op->template getSuccessResult<Data>();
}

template class TermCodeTree<false, TermLiteralClause>;
template class TermCodeTree<true,  TermLiteralClause>;
template class TermCodeTree<false, DemodulatorData>;
template class TermCodeTree<true,  DemodulatorData>;

};
