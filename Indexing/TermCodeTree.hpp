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
#include "Lib/Stack.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

template<bool higherOrder, class Data>
class TermCodeTree : public CodeTree 
{
protected:
  static void onCodeOpDestroying(CodeOp* op);
  
public:
  TermCodeTree();

  void insert(Data* data);
  void remove(const Data& data);

private:
  struct RemovingTermMatcher
  : public Matcher</*removing*/true,false,higherOrder>
  {
  public:
    using Base = Matcher</*removing*/true,false,higherOrder>;

    void init(FlatTerm* ft_, TermCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);
  };

public:
  struct TermMatcher
  : public Matcher</*removing*/false,false,higherOrder>
  {
    TermMatcher();

    using Base = Matcher</*removing*/false,false,higherOrder>;
    using Base::ft;

    #ifdef JIT_VERIFY_MATCHES
      /** Query term of the current retrieval, kept so verifyMatch can check
      *  that every returned generalization really instantiates to it. */
      TermList _query;
      /** Differential oracle for the term-matching path: check that d->term
      *  under the bindings the matcher produced equals the query, and print
      *  "% JITDIFF ..." if not. Build with -DJIT_VERIFY_MATCHES; costs one
      *  substitution application per result, so it is off by default.
      *  Caught the ASSIGN_VAR/r11 clobber (see CopyPatchJit emitPushAlt). */
      void verifyMatch(Data* d);
    #endif

    void init(CodeTree* tree, TermList t);
    void reset();
    
    Data* next();
    
    USE_ALLOCATOR(TermMatcher);
  };

};

};

#endif // __TermCodeTree__
