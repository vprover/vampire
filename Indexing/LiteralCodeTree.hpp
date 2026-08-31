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

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class LiteralCodeTree : public CodeTree
{
public:
  LiteralCodeTree();

  void insert(Data* data);
  void remove(const Data& data);

  struct LiteralMatcher
  : public Matcher</*removing=*/false,/*checkRange=*/false,/*higherOrder=*/false>
  {
    void init(const CodeTree& tree, Literal* lit, bool complementary);
    void reset();

    Data* next();

  private:
    bool _checkEqReversed;
  };

private:
  void onCodeOpDestroying(CodeOp* op) override;
};

};

#endif // __LiteralCodeTree__
