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
 * @file LiteralCodeTree.cpp
 * Implements class LiteralCodeTree.
 */

#include "Kernel/FlatTerm.hpp"
#include "Kernel/Term.hpp"

#include "Index.hpp"

#include "LiteralCodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

template<class Data>
void LiteralCodeTree<Data>::onCodeOpDestroying(CodeOp* op)
{
  if (op->isSuccess()) {
    delete op->getSuccessResult<Data>();
  }
}

template<class Data>
LiteralCodeTree<Data>::LiteralCodeTree()
{
  _clauseCodeTree = false;
  _onCodeOpDestroying = onCodeOpDestroying;
}

template<class Data>
void LiteralCodeTree<Data>::insert(Data* data)
{
  Recycled<CodeStack> code;

  TermCompiler compiler(*code);
  compiler.handleTerm(data->literal);
  code->push(CodeOp::getSuccess(data));

  compiler.updateCodeTree(this);

  incorporate(*code);
  ASS(code->isEmpty());
}

template<class Data>
void LiteralCodeTree<Data>::remove(const Data& data)
{
  static RemovingLiteralMatcher rtm;
  static Stack<CodeOp*> firstsInBlocks;
  firstsInBlocks.reset();

  auto ft = FlatTerm::create(data.literal);
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
}

template<class Data>
void LiteralCodeTree<Data>::RemovingLiteralMatcher::init(FlatTerm* ft_,
					     LiteralCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  Matcher::init(tree_, tree_->getEntryPoint(), 0, 0, firstsInBlocks_);

  firstsInBlocks->push(entry);

  ft = ft_;
  tp = 0;
  op = entry;
}

template<class Data>
void LiteralCodeTree<Data>::LiteralMatcher::init(CodeTree* tree, Literal* lit, bool complementary)
{
  Matcher::init(tree,tree->getEntryPoint(), 0, 0);

  ASS(!ft);
  ft = FlatTerm::create(lit);
  if (complementary) {
    ft->changeLiteralPolarity();
  }
  tp = 0;
  op = entry;
  _checkEqReversed = lit->isEquality();
}

template<class Data>
void LiteralCodeTree<Data>::LiteralMatcher::reset()
{
  ft->destroy();
  ft = nullptr;
}

template<class Data>
Data* LiteralCodeTree<Data>::LiteralMatcher::next()
{
  if (finished()) {
    //all possible matches are exhausted
    return 0;
  }

MATCH:
  _matched = execute();
  if (!_matched) {
    if (_checkEqReversed) {
      ft->swapCommutativePredicateArguments();
      Matcher::init(tree,tree->getEntryPoint(), 0, 0);
      tp = 0;
      op = entry;
      _checkEqReversed = false;
      goto MATCH;
    }
    return 0;
  }

  ASS(op->isSuccess());
  return op->getSuccessResult<Data>();
}

template class LiteralCodeTree<LiteralClause>;

};
