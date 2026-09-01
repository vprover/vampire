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
  CodeTree::_containsLiterals = true;
}

template<bool higherOrder, class Data>
void LiteralCodeTree<higherOrder, Data>::insert(Data* data)
{
  Recycled<CodeTree::CodeStack> code;

  CodeTree::TermCompiler compiler(*code);
  compiler.handleTerm(data->key());
  code->push(CodeTree::CodeOp::getSuccess(data));

  compiler.updateCodeTree(this);

  CodeTree::incorporate(*code);
  ASS(code->isEmpty());
}

template<bool higherOrder, class Data>
void LiteralCodeTree<higherOrder, Data>::LiteralMatcher::init(const CodeTree& tree, Literal* lit, bool complementary)
{
  Base::init(tree,tree.getEntryPoint(), 0, 0);

  ASS(!ft);
  ft = FlatTerm::create(TermList(lit));
  if (complementary) {
    ft->changeLiteralPolarity();
  }
  Base::tp = 0;
  Base::op = Base::entry;
  _checkEqReversed = lit->isEquality();
}

template<bool higherOrder, class Data>
Data* LiteralCodeTree<higherOrder, Data>::LiteralMatcher::next()
{
  if (Base::finished()) {
    //all possible matches are exhausted
    return 0;
  }

MATCH:
  Base::_matched = Base::execute();
  if (!Base::_matched) {
    if (_checkEqReversed) {
      ft->swapCommutativePredicateArguments();
      Base::init(*Base::tree,Base::tree->getEntryPoint(), 0, 0);
      Base::tp = 0;
      Base::op = Base::entry;
      _checkEqReversed = false;
      goto MATCH;
    }
    return 0;
  }

  ASS(Base::op->isSuccess());
  return Base::op->template getSuccessResult<Data>();
}

template class LiteralCodeTree<false, LiteralClause>;
template class LiteralCodeTree<true, LiteralClause>;

};
