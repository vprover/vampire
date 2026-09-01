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
  LiteralCodeTree();

  void insert(Data* data);

  struct LiteralMatcher
  : public TermOrLiteralCodeTree<higherOrder, Data>::Matcher
  {
    using Base = TermOrLiteralCodeTree<higherOrder, Data>::Matcher;
    using Base::ft;

    void init(const CodeTree& tree, Literal* lit, bool complementary);
    Data* next();

  private:
    bool _checkEqReversed;
  };
};

};

#endif // __LiteralCodeTree__
