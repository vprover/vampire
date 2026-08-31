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

#include "Lib/Allocator.hpp"

#include "Kernel/TypedTermList.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class TermCodeTree : public CodeTree
{
protected:
  void onCodeOpDestroying(CodeOp* op) override;
  void printSuccess(std::ostream& out, const CodeOp& op) const override;

public:
  void insert(Data* data);
  void remove(const Data& data);

public:
  struct TermMatcher
  : public Matcher</*removing*/false,false,higherOrder>
  {
    TermMatcher();

    using Base = Matcher</*removing*/false,false,higherOrder>;
    using Base::ft;

    void init(const CodeTree& tree, TypedTermList t);
    void reset();

    Data* next();

    USE_ALLOCATOR(TermMatcher);
  private:
    TermList _querySort;
  };

};

};

#endif // __TermCodeTree__
