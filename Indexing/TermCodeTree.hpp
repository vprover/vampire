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
 * @file TermCodeTree.hpp
 * Defines class TermCodeTree.
 */

#ifndef __TermCodeTree__
#define __TermCodeTree__

#include "Forwards.hpp"

#include "Kernel/TypedTermList.hpp"

#include "TermOrLiteralCodeTree.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class TermCodeTree : public TermOrLiteralCodeTree<higherOrder, Data>
{
public:
  void insert(Data* data);

  struct TermMatcher
  : public TermOrLiteralCodeTree<higherOrder, Data>::Matcher
  {
    using Base = TermOrLiteralCodeTree<higherOrder, Data>::Matcher;
    using Base::ft;

    void init(const CodeTree& tree, TypedTermList t);
    Data* next();

  private:
    TermList _querySort;
  };

};

};

#endif // __TermCodeTree__
