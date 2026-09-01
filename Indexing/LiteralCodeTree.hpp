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
 * @file LiteralCodeTree.hpp
 * Defines class LiteralCodeTree.
 */

#ifndef __LiteralCodeTree__
#define __LiteralCodeTree__

#include "Forwards.hpp"

#include "Lib/Vector.hpp"

#include "TermOrLiteralCodeTree.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class LiteralCodeTree : public TermOrLiteralCodeTree<higherOrder, Data>
{
public:
  LiteralCodeTree() {
    CodeTree::_containsLiterals = true;
  }

  struct LiteralMatcher
  : public TermOrLiteralCodeTree<higherOrder, Data>::Matcher
  {
    using Base = TermOrLiteralCodeTree<higherOrder, Data>::Matcher;
    using Base::ft;

    void init(const CodeTree& tree, Literal* lit, bool complementary) {
      Base::init(tree, FlatTerm::create(TermList(lit)));
      if (complementary) {
        ft->changeLiteralPolarity();
      }
      _checkEqReversed = lit->isEquality();
    }

    Data* next() {
      if (Base::finished()) {
        //all possible matches are exhausted
        return nullptr;
      }

MATCH:
      Base::_matched = Base::execute();
      if (!Base::_matched) {
        if (_checkEqReversed) {
          Base::init(*Base::tree, Base::ft);
          ft->swapCommutativePredicateArguments();
          _checkEqReversed = false;
          goto MATCH;
        }
        return nullptr;
      }

      ASS(Base::op->isSuccess());
      return Base::op->template getSuccessResult<Data>();
    }

  private:
    bool _checkEqReversed;
  };
};

};

#endif // __LiteralCodeTree__
