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
 * @file TermOrLiteralCodeTree.hpp
 * Defines class TermOrLiteralCodeTree.
 */

#ifndef __TermOrLiteralCodeTree__
#define __TermOrLiteralCodeTree__

#include "Forwards.hpp"

#include "CodeTree.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/TypedTermList.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class TermOrLiteralCodeTree : public CodeTree
{
protected:
  void onCodeOpDestroying(CodeOp* op) override {
    if (op->isSuccess()) {
      delete op->getSuccessResult<Data>();
    }
  }
  void printSuccess(std::ostream& out, const CodeOp& op) const override
  { out << *op.getSuccessResult<Data>(); }

public:
  void insert(Data* data)
  {
    Recycled<CodeStack> code;

    TypedTermList t(data->key());
    if (t.isVar()) {
      code->push(CodeOp::getTermOp(ASSIGN_VAR,0));
      // we match the variable sort separately, but the binding array has to be prepared
      for (const auto& v : iterTraits(VariableIterator(t.sort()))) {
        ASS_G(v.var(), 0); // X0 is reserved for the term itself
        if (v.var()+1 > _maxVarCnt) { _maxVarCnt = v.var()+1; }
      }
    }
    else {
      ASS(t.isTerm());

      TermCompiler compiler(*code);
      compiler.handleTerm(t.term());
      compiler.updateCodeTree(this);
    }

    code->push(CodeOp::getSuccess(data));
    incorporate(*code);
    //@b incorporate should empty the code stack
    ASS(code->isEmpty());
  }

  void remove(const Data& data) {
    Recycled<RemovingMatcher> rtm;
    Recycled<Stack<CodeOp*>> firstsInBlocks;

    FlatTerm* ft=FlatTerm::create(TermList(data.key()));
    rtm->init(ft, *this, &*firstsInBlocks);

    Data* dptr = nullptr;
    for(;;) {
      if (!rtm->execute()) {
        ASSERTION_VIOLATION;
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

    optimizeMemoryAfterRemoval(&*firstsInBlocks, rtm->op);
  }

public:
  struct RemovingMatcher
  : public Matcher</*removing=*/true,/*checkRange=*/false,higherOrder>
  {
  public:
    using Base = Matcher</*removing*/true,/*checkRange=*/false,higherOrder>;
    using Base::ft;

    void init(FlatTerm* ft_, const CodeTree& tree_, Stack<CodeOp*>* firstsInBlocks_) {
      Base::init(tree_, tree_.getEntryPoint(), /*linfos_=*/0, /*linfoCnt_=*/0, firstsInBlocks_);
      Base::firstsInBlocks->push(Base::entry);
      ft=ft_;
      Base::tp=0;
      Base::op=Base::entry;
    }
    void reset() {
      ft->destroy();
      ft = nullptr;
    }
  };

  struct Matcher
  : public CodeTree::Matcher</*removing*/false,/*checkRange=*/false,higherOrder>
  {
    using Base = CodeTree::Matcher</*removing*/false,/*checkRange=*/false,higherOrder>;
    using Base::ft;

    void init(const CodeTree& tree, FlatTerm* ft_) {
      Base::init(tree,tree.getEntryPoint(), 0, 0);
      ft = ft_;
      Base::tp = 0;
      Base::op = Base::entry;
    }

    void reset() {
      ft->destroy();
      ft = nullptr;
    }
  };

};

};

#endif // __TermOrLiteralCodeTree__
