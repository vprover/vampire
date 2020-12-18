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
 * @file ClauseCodeTree.hpp
 * Defines class ClauseCodeTree.
 */

#ifndef __ClauseCodeTree__
#define __ClauseCodeTree__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseCodeTree : public CodeTree
{
protected:
  static void onCodeOpDestroying(CodeOp* op);
  
public:
  ClauseCodeTree();

  void insert(Clause* cl);
  void remove(Clause* cl);

private:

  //////// insertion //////////

  struct InitialLiteralOrderingComparator;

  void optimizeLiteralOrder(DArray<Literal*>& lits);
  void evalSharing(Literal* lit, CodeOp* startOp, size_t& sharedLen, size_t& unsharedLen, CodeOp*& nextOp);
  static void matchCode(CodeStack& code, CodeOp* startOp, size_t& matchedCnt, CodeOp*& nextOp);

  //////// removal //////////

  bool removeOneOfAlternatives(CodeOp* op, Clause* cl, Stack<CodeOp*>* firstsInBlocks);

  struct RemovingLiteralMatcher
  : public RemovingMatcher
  {
    void init(CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_,
	ClauseCodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);

    CLASS_NAME(ClauseCodeTree::RemovingLiteralMatcher);
    USE_ALLOCATOR(RemovingLiteralMatcher);
  };

  //////// retrieval //////////

  /** Context for finding matches of literals
   *
   * Here the actual execution of the code of the tree takes place */
  struct LiteralMatcher
  : public Matcher
  {
    void init(CodeTree* tree, CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_, bool seekOnlySuccess=false);
    bool next();
    bool doEagerMatching();

    inline bool eagerlyMatched() const { return _eagerlyMatched; }

    inline ILStruct* getILS() { ASS(matched()); return op->getILS(); }

    CLASS_NAME(ClauseCodeTree::LiteralMatcher);
    USE_ALLOCATOR(LiteralMatcher);

  private:
    bool _eagerlyMatched;

    Stack<CodeOp*> eagerResults;

    void recordMatch();
  };

public:
  struct ClauseMatcher
  {
    void init(ClauseCodeTree* tree_, Clause* query_, bool sres_);
    void deinit();

    Clause* next(int& resolvedQueryLit);

    bool matched() { return lms.isNonEmpty() && lms.top()->success(); }
    CodeOp* getSuccessOp() { ASS(matched()); return lms.top()->op; }

    CLASS_NAME(ClauseCodeTree::ClauseMatcher);
    USE_ALLOCATOR(ClauseMatcher);

  private:
    void enterLiteral(CodeOp* entry, bool seekOnlySuccess);
    void leaveLiteral();
    bool canEnterLiteral(CodeOp* op);

    bool checkCandidate(Clause* cl, int& resolvedQueryLit);
    bool matchGlobalVars(int& resolvedQueryLit);
    bool compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq);

    bool existsCompatibleMatch(ILStruct* si, MatchInfo* sq, ILStruct* oi);

    Clause* query;
    ClauseCodeTree* tree;
    bool sres;

    static const unsigned sresNoLiteral=static_cast<unsigned>(-1);
    unsigned sresLiteral;

    /**
     * Literal infos that we will attempt to match
     * For each equality we add two lit infos, once with reversed arguments.
     * The order of infos is:
     *
     * Ground literals
     * Non-ground literals
     * [if sres] Ground literals negated
     * [if sres] Non-ground literals negated
     */
    DArray<LitInfo> lInfos;

    Stack<LiteralMatcher*> lms;
  };

private:

  //////// member variables //////////

#if VDEBUG
  unsigned _clauseMatcherCounter;
#endif

};


};

#endif // __ClauseCodeTree__
