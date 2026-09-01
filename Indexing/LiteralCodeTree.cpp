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

template<bool higherOrder, class Data>
LiteralCodeTree<higherOrder, Data>::LiteralCodeTree()
{
  _containsLiterals = true;
}

template<bool higherOrder, class Data>
void LiteralCodeTree<higherOrder, Data>::insert(Data* data)
{
  Recycled<CodeStack> code;

  TermCompiler compiler(*code);
  compiler.handleTerm(data->key());
  code->push(CodeOp::getSuccess(data));

  compiler.updateCodeTree(this);

  incorporate(*code);
  ASS(code->isEmpty());
}

template<bool higherOrder, class Data>
void LiteralCodeTree<higherOrder, Data>::remove(const Data& data)
{
  Recycled<RemovingMatcher<higherOrder>> rtm;
  Recycled<Stack<CodeOp*>> firstsInBlocks;

  auto ft = FlatTerm::create(TermList(data.literal));
  rtm->init(ft, *this, &*firstsInBlocks);

  Data* dptr = nullptr;
  for(;;) {
    if (!rtm->execute()) {
      INVALID_OPERATION("term being removed was not found");
    }
    ASS(rtm->op->isSuccess());
    dptr=rtm->op->template getSuccessResult<Data>();
    if (*dptr==data) {
      break;
    }
  }

  rtm->op->makeFail();

  ASS(dptr);
  delete dptr;
  ft->destroy();

  optimizeMemoryAfterRemoval(&*firstsInBlocks, rtm->op);
}

template<bool higherOrder, class Data>
void LiteralCodeTree<higherOrder, Data>::LiteralMatcher::init(const CodeTree& tree, Literal* lit, bool complementary)
{
  Matcher::init(tree,tree.getEntryPoint(), 0, 0);

  ASS(!ft);
  ft = FlatTerm::create(TermList(lit));
  if (complementary) {
    ft->changeLiteralPolarity();
  }
  tp = 0;
  op = entry;
  _checkEqReversed = lit->isEquality();
}

template<bool higherOrder, class Data>
Data* LiteralCodeTree<higherOrder, Data>::LiteralMatcher::next()
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
      Matcher::init(*tree,tree->getEntryPoint(), 0, 0);
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

template class LiteralCodeTree<false, LiteralClause>;
template class LiteralCodeTree<true, LiteralClause>;

};
