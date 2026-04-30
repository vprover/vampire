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

#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<class Data>
class LiteralCodeTree : public CodeTree
{
public:
  LiteralCodeTree();

  void insert(Data* data);
  void remove(const Data& data);

  struct LiteralMatcher
  : public Matcher</*removing=*/false,/*checkRange=*/false,/*higherOrder=*/false>
  {
    void init(CodeTree* tree, Literal* lit, bool complementary);
    void reset();

    Data* next();

  private:
    bool _checkEqReversed;
  };

private:
  void onCodeOpDestroying(CodeOp* op) override;

  struct RemovingLiteralMatcher
  : public Matcher</*removing*/true,/*checkRange=*/false,/*higherOrder=*/false>
  {
  public:
    void init(FlatTerm* ft_, LiteralCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);
  };
};

};

#endif // __LiteralCodeTree__
