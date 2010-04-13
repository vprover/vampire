/**
 * @file ClauseCodeTree.hpp
 * Defines class ClauseCodeTree.
 */

#ifndef __ClauseCodeTree__
#define __ClauseCodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Stack.hpp"

#include "Index.hpp"

#include "CodeTree.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseCodeTree : public CodeTree
{
public:
  ClauseCodeTree();
  
  void insert(Clause* cl);
  void remove(Clause* cl);

private:

  //////// insertion //////////

  void optimizeLiteralOrder(DArray<Literal*>& lits);
  void evalSharing(Literal* lit, OpCode* startOp, size_t& sharedLen, size_t& unsharedLen);
  static void matchCode(CodeStack& code, OpCode* startOp, size_t& matchedCnt);

  //////// removal //////////
  
  bool removeOneOfAlternatives(OpCode* op, Clause* cl, Stack<OpCode*>* firstsInBlocks);
  
  struct RemovingLiteralMatcher
  : public RemovingMatcher
  {
    void init(OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_,
	ClauseCodeTree* tree_, Stack<OpCode*>* firstsInBlocks_);

    CLASS_NAME("ClauseCodeTree::RemovingLiteralMatcher");
    USE_ALLOCATOR(RemovingLiteralMatcher);
  };
  
  //////// retrieval //////////

  /** Context for finding matches of literals
   *
   * Here the actual execution of the code of the tree takes place */
  struct LiteralMatcher
  : public Matcher
  {
    void init(CodeTree* tree, OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_, bool seekOnlySuccess=false);
    bool next();
    bool doEagerMatching();
    
    inline bool eagerlyMatched() const { return _eagerlyMatched; }

    inline ILStruct* getILS() { ASS(matched()); return op->getILS(); }

    CLASS_NAME("ClauseCodeTree::LiteralMatcher");
    USE_ALLOCATOR(LiteralMatcher);

  private:
    bool _eagerlyMatched;
    
    Stack<OpCode*> eagerResults;

    void recordMatch();
  };

public:
  struct ClauseMatcher
  {
    void init(ClauseCodeTree* tree_, Clause* query_, bool sres_);
    void deinit();

    Clause* next(int& resolvedQueryLit);
    
    bool matched() { return lms.isNonEmpty() && lms.top()->success(); }
    OpCode* getSuccessOp() { ASS(matched()); return lms.top()->op; }

    CLASS_NAME("ClauseCodeTree::ClauseMatcher");
    USE_ALLOCATOR(ClauseMatcher);
    
  private:
    void enterLiteral(OpCode* entry, bool seekOnlySuccess);
    void leaveLiteral();
    bool litEndAlreadyVisited(OpCode* op);
    
    bool checkCandidate(Clause* cl, int& resolvedQueryLit);
    bool matchGlobalVars(int& resolvedQueryLit);
    bool compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq);

    Clause* query;
    ClauseCodeTree* tree;
    bool sres;

    static const unsigned sresNoLiteral=static_cast<unsigned>(-1);
    unsigned sresLiteral;

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
