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
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"
#include "Debug/TimeProfiling.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Recycled.hpp"
#include "Lib/TriangularArray.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

#include "ClauseCodeTree.hpp"

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

namespace Indexing
{

using namespace std;
using namespace Lib;
using namespace Kernel;

void ClauseCodeTree::onCodeOpDestroying(CodeOp* op)
{
  if (op->isLitEnd()) {
    delete op->getILS(); 
  }
}

void ClauseCodeTree::printSuccess(std::ostream& out, const CodeOp& op) const
{
  out << op.getSuccessResult<Clause>()->toString();
}

ClauseCodeTree::ClauseCodeTree()
{
  _clauseCodeTree = true;
#if VDEBUG
  _clauseMatcherCounter=0;
#endif
}

//////////////// insertion ////////////////////

void ClauseCodeTree::insert(Clause* cl)
{
  // Insertion is three phases that do quite different things, and only their sum was
  // visible before. Each scope is entered once per inserted clause, so the three
  // together cost ~0.02% of a sweep -- see the comment in ClauseMatcher::init for the
  // arithmetic and for what is deliberately left unmeasured.
  unsigned clen=cl->length();
  static DArray<Literal*> lits;
  lits.initFromArray(clen, *cl);

  {
    // The greedy heuristic that decides which literal to compile first. It is quadratic
    // in the clause length -- for each start position it walks every remaining literal's
    // code against the tree (evalSharing) -- and it compiles all of them to do so, so
    // the compilation below is the second time each literal is compiled.
    TIME_TRACE("codetree literal ordering");
    optimizeLiteralOrder(lits);
  }

  CodeStack code;

  {
    TIME_TRACE("codetree code compilation");
    LitCompiler compiler(code);

    for(unsigned i=0;i<clen;i++) {
      compiler.nextLit();
      compiler.handleTerm(lits[i]);
    }
    code.push(CodeOp::getSuccess(cl));

    compiler.updateCodeTree(this);
  }

  {
    // Merging the fresh code into the tree: finding how far it matches an existing path,
    // splitting a block, and rebuilding the search structures (compressCheckOps).
    TIME_TRACE("codetree code incorporation");
    incorporate(code);
  }
  ASS(code.isEmpty());
}

struct ClauseCodeTree::InitialLiteralOrderingComparator
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    if(l1->weight()!=l2->weight()) {
      return Int::compare(l2->weight(), l1->weight());
    }
    return Int::compare(l1->getId(), l2->getId());
  }
};

void ClauseCodeTree::optimizeLiteralOrder(DArray<Literal*>& lits)
{
  lits.sort(InitialLiteralOrderingComparator());

  unsigned clen=lits.size();
  if(isEmpty() || clen<=1) {
    return;
  }

  CodeStack code;
  LitCompiler compiler(code);
  DArray<CodeStack> codes(clen);
  for (unsigned i = 0; i < clen; i++) {
    compiler.nextLit();
    compiler.handleTerm(lits[i]);
    codes[i] = std::move(code);
  }

  CodeOp* entry=getEntryPoint();
  for(unsigned startIndex=0;startIndex<clen-1;startIndex++) {
//  for(unsigned startIndex=0;startIndex<1;startIndex++) {

    size_t unshared=1;
    unsigned bestIndex=startIndex;
    size_t bestSharedLen;
    bool bestGround=lits[startIndex]->ground();
    CodeOp* nextOp;
    evalSharing(codes[startIndex], entry, bestSharedLen, unshared, nextOp);
    if(!unshared) {
      goto have_best;
    }

    for(unsigned i=startIndex+1;i<clen;i++) {
      size_t sharedLen;
      evalSharing(codes[i], entry, sharedLen, unshared, nextOp);
      if(!unshared) {
	bestIndex=i;
        goto have_best;
      }

      if(sharedLen>bestSharedLen && (!bestGround || lits[i]->ground()) ) {
//	cout<<lits[i]->toString()<<" is better than "<<lits[bestIndex]->toString()<<endl;
	bestSharedLen=sharedLen;
	bestIndex=i;
	bestGround=lits[i]->ground();
      }
    }

  have_best:
    swap(lits[startIndex],lits[bestIndex]);
    swap(codes[startIndex], codes[bestIndex]);

    if(unshared) {
      //we haven't matched the whole literal, so we won't proceed with the next one
      break;
    }
    ASS(nextOp);
    entry=nextOp;
  }
  for (auto& literal : codes) {
    delete literal.top().getILS();
  }
}

void ClauseCodeTree::evalSharing(CodeStack& code, CodeOp* startOp, size_t& sharedLen, size_t& unsharedLen, CodeOp*& nextOp)
{
  matchCode(code, startOp, sharedLen, nextOp);

  unsharedLen=code.size()-sharedLen;

  ASS(code.top().isLitEnd());
}

/**
 * Match the operations in @b code CodeStack on the code starting at @b startOp.
 *
 * Into @b matchedCnt assign number of matched operations and into @b lastAttemptedOp
 * the last operation on which we have attempted matching. If @b matchedCnt==code.size(),
 * the @b lastAttemptedOp is equal to the last operation in the @b code stack, otherwise
 * it is the first operation on which mismatch occurred and there was no alternative to
 * proceed to (in this case it therefore holds that @b lastAttemptedOp->alternative==0 ).
 */
void ClauseCodeTree::matchCode(CodeStack& code, CodeOp* startOp, size_t& matchedCnt, CodeOp*& nextOp)
{
  size_t clen=code.length();
  CodeOp* treeOp=startOp;

  for(size_t i=0;i<clen;i++) {
    for(;;) {
      if(treeOp->isSearchStruct()) {
	SearchStruct* ss=treeOp->getSearchStruct();
	CodeOp** toPtr;
	if(ss->getTargetOpPtr<false>(code[i], toPtr) && *toPtr) {
	  treeOp=*toPtr;
	  continue;
	}
      }
      else if(code[i].equalsForOpMatching(*treeOp)) {
	break;
      }
      ASS_NEQ(treeOp,treeOp->alternative());
      treeOp=treeOp->alternative();
      if(!treeOp) {
	matchedCnt=i;
	nextOp=0;
	return;
      }
    }

    //the SEARCH_STRUCT operation does not occur in a CodeBlock
    ASS(!treeOp->isSearchStruct());
    //we can safely do increase because as long as we match and something
    //remains in the @b code stack, we aren't at the end of the CodeBlock
    //either (as each code block contains at least one FAIL or SUCCESS
    //operation, and CodeStack contains at most one SUCCESS as the last
    //operation)
    treeOp++;
  }
  //we matched the whole CodeStack
  matchedCnt=clen;
  nextOp=treeOp;
}


//////////////// removal ////////////////////

void ClauseCodeTree::remove(Clause* cl)
{
  static DArray<LitInfo> lInfos;
  Recycled<Stack<CodeOp*>> firstsInBlocks;
  Recycled<Stack<Recycled<RemovingLiteralMatcher, NoReset>>> rlms;

  unsigned clen=cl->length();
  lInfos.ensure(clen);

  if(!clen) {
    CodeOp* op=getEntryPoint();
    firstsInBlocks->push(op);
    if(!removeOneOfAlternatives(op, cl, &*firstsInBlocks)) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("empty clause to be removed was not found");
    }
    return;
  }

  for(unsigned i=0;i<clen;i++) {
    lInfos[i]=LitInfo(cl,i);
    lInfos[i].liIndex=i;
  }
  incTimeStamp();

  CodeOp* op=getEntryPoint();
  firstsInBlocks->push(op);
  unsigned depth=0;
  for(;;) {
    RemovingLiteralMatcher* rlm = 0;
    {
      Recycled<RemovingLiteralMatcher, NoReset> rrlm; // take rlm out of recycling
      rlm = &*rrlm; // get the actual content (also to use after this initialization block)
      rlm->init(op, lInfos.array(), lInfos.size(), *this, &*firstsInBlocks); // init it
      rlms->push(std::move(rrlm)); // store it in rlms (along with the obligation to return to recycling when no longer used)
    }

  iteration_restart:
    if(!rlm->execute()) {
      if(depth==0) {
        ASSERTION_VIOLATION;
        INVALID_OPERATION("clause to be removed was not found");
      }
      rlms->pop();
      depth--;
      rlm = &*rlms->top();
      goto iteration_restart;
    }

    op=rlm->op;
    ASS(op->isLitEnd());
    ASS_EQ(op->getILS()->depth, depth);

    if(op->getILS()->timestamp==_curTimeStamp) {
      //we have already been here
      goto iteration_restart;
    }
    op->getILS()->timestamp=_curTimeStamp;

    op++;
    if(depth==clen-1) {
      if(removeOneOfAlternatives(op, cl, &*firstsInBlocks)) {
        //successfully removed
        break;
      }
      goto iteration_restart;
    }
    ASS_L(depth,clen-1);
    depth++;
  }

  for(unsigned i=0;i<clen;i++) {
    lInfos[i].dispose();
  }
}

void ClauseCodeTree::RemovingLiteralMatcher::init(CodeOp* entry_, LitInfo* linfos_,
    size_t linfoCnt_, const ClauseCodeTree& tree_, Stack<CodeOp*>* firstsInBlocks_)
{
  Matcher::init(tree_, entry_, linfos_, linfoCnt_, firstsInBlocks_);

  ALWAYS(prepareLiteral());
}

/**
 * The first operation of the CodeBlock containing @b op
 * must already be on the @b firstsInBlocks stack.
 */
bool ClauseCodeTree::removeOneOfAlternatives(CodeOp* op, Clause* cl, Stack<CodeOp*>* firstsInBlocks)
{
  unsigned initDepth=firstsInBlocks->size();

  while(!op->isSuccess() || op->getSuccessResult<Clause>()!=cl) {
    op=op->alternative();
    if(!op) {
      firstsInBlocks->truncate(initDepth);
      return false;
    }
    firstsInBlocks->push(op);
  }
  op->makeFail();
  optimizeMemoryAfterRemoval(firstsInBlocks, op);
  return true;
}

//////////////// retrieval ////////////////////

////////// LiteralMatcher

/**
 * If @b seekOnlySuccess if true, we will look only for immediate SUCCESS operations
 *  and fail if there isn't any at the beginning (possibly also among alternatives).
 */
void ClauseCodeTree::LiteralMatcher::init(const CodeTree& tree_, CodeOp* entry_,
					  LitInfo* linfos_, size_t linfoCnt_,
					  bool seekOnlySuccess)
{
  ASS_G(linfoCnt_,0);

  Matcher::init(tree_,entry_,linfos_,linfoCnt_);

  _eagerlyMatched=false;
  eagerResults.reset();

  RSTAT_CTR_INC("LiteralMatcher::init");
  if(seekOnlySuccess) {
    RSTAT_CTR_INC("LiteralMatcher::init - seekOnlySuccess");
    //we are interested only in SUCCESS operations
    //(and those must be at the entry point or its alternatives)

    _eagerlyMatched=true;
    fresh=false;
    CodeOp* sop=entry;
    while(sop) {
      if(sop->isSuccess()) {
        eagerResults.push(sop);
      }
      sop=sop->alternative();
    }
    return;
  }

  ALWAYS(prepareLiteral());
}

/**
 * Try to find a match, and if one is found, return true
 */
bool ClauseCodeTree::LiteralMatcher::next()
{
  if(eagerlyMatched()) {
    _matched=!eagerResults.isEmpty();
    if(!_matched) {
      return false;
    }
    op=eagerResults.pop();
    return true;
  }

  if(finished()) {
    //all possible matches are exhausted
    return false;
  }

  _matched=execute();
  if(!_matched) {
    return false;
  }

  ASS(op->isLitEnd() || op->isSuccess());
  if(op->isLitEnd()) {
    recordMatch();
  }
  return true;
}

/**
 * Perform eager matching and return true iff new matches were found
 */
bool ClauseCodeTree::LiteralMatcher::doEagerMatching()
{
  ASS(!eagerlyMatched()); //eager matching can be done only once
  ASS(eagerResults.isEmpty());
  ASS(!finished());

  //backup the current op
  CodeOp* currOp=op;

  static Stack<CodeOp*> eagerResultsRevOrder;
  static Stack<CodeOp*> successes;
  eagerResultsRevOrder.reset();
  successes.reset();

  while(execute()) {
    if(op->isLitEnd()) {
      recordMatch();
      eagerResultsRevOrder.push(op);
    }
    else {
      ASS(op->isSuccess());
      successes.push(op);
    }
  }

  //we want to yield results in the order we found them
  //(otherwise the subsumption resolution would be preferred to the
  //subsumption)
  while(eagerResultsRevOrder.isNonEmpty()) {
    eagerResults.push(eagerResultsRevOrder.pop());
  }
  //we want to yield SUCCESS operations first (as after them there may
  //be no need for further clause retrieval)
  while(successes.isNonEmpty()) {
    eagerResults.push(successes.pop());
  }

  _eagerlyMatched=true;

  op=currOp; //restore the current op

  return eagerResults.isNonEmpty();
}

void ClauseCodeTree::LiteralMatcher::recordMatch()
{
  ASS(_matched);

  ILStruct* ils=op->getILS();
  ils->ensureFreshness(tree->_curTimeStamp);
  if(ils->finished) {
    //no need to record matches which we already know will not lead to anything
    return;
  }
  if(!ils->matchCnt && linfos[curLInfo].opposite) {
    //if we're matching opposite matches, we have already tried all non-opposite ones
    ils->noNonOppositeMatches=true;
  }
  ils->addMatch(linfos[curLInfo].liIndex, bindings);
}


////////// ClauseMatcher

/**
 * Initialize the ClauseMatcher to retrieve generalizetions
 * of the @b query_ clause.
 * If @b sres_ if true, we perform subsumption resolution
 */
void ClauseCodeTree::ClauseMatcher::init(ClauseCodeTree* tree_, Clause* query_, bool sres_)
{
  // "codetree forward subsumption" is 18% of a sweep's instructions and was one opaque
  // number. These three scopes -- setup here, teardown in reset(), and the multi-literal
  // matching in checkCandidate() -- cut it into the parts that are not the code-tree
  // interpreter, so that what is left as this node's *self* time is the interpreter and
  // only the interpreter.
  //
  // The interpreter itself is deliberately not entered. Matcher::execute() dispatches on
  // one CodeOp at a time, so a scope inside it would be measuring itself: at ~107
  // instructions per scope it would cost more than the ops it timed. Measuring it as a
  // whole, against named siblings, is as far as this can usefully go.
  //
  // Cost of the three: init and reset run once per perform() (7.2 G calls corpus-wide,
  // so ~0.06% of corpus each), checkCandidate once per candidate clause that survives to
  // a SUCCESS op and has more than one literal -- per candidate, never per CodeOp.
  TIME_TRACE("codetree matcher setup");

  ASS(!tree_->isEmpty());

  query=query_;
  tree=tree_;
  sres=sres_;
  lms.reset();

#if VDEBUG
  ASS_EQ(tree->_clauseMatcherCounter,0);
  tree->_clauseMatcherCounter++;
#endif

  //init LitInfo records
  unsigned clen=query->length();
  unsigned baseLICnt=clen;
  for(unsigned i=0;i<clen;i++) {
    if((*query)[i]->isEquality()) {
      baseLICnt++;
    }
  }
  unsigned liCnt=sres ? (baseLICnt*2) : baseLICnt;
  lInfos.ensure(liCnt);

  //we put ground literals first
  unsigned liIndex=0;
  for(unsigned i=0;i<clen;i++) {
    if(!(*query)[i]->ground()) {
      continue;
    }
    lInfos[liIndex]=LitInfo(query,i);
    lInfos[liIndex].liIndex=liIndex;
    liIndex++;
    if((*query)[i]->isEquality()) {
      lInfos[liIndex]=LitInfo::getReversed(lInfos[liIndex-1]);
      lInfos[liIndex].liIndex=liIndex;
      liIndex++;
    }
  }
  for(unsigned i=0;i<clen;i++) {
    if((*query)[i]->ground()) {
      continue;
    }
    lInfos[liIndex]=LitInfo(query,i);
    lInfos[liIndex].liIndex=liIndex;
    liIndex++;
    if((*query)[i]->isEquality()) {
      lInfos[liIndex]=LitInfo::getReversed(lInfos[liIndex-1]);
      lInfos[liIndex].liIndex=liIndex;
      liIndex++;
    }
  }
  if(sres) {
    for(unsigned i=0;i<baseLICnt;i++) {
      unsigned newIndex=i+baseLICnt;
      lInfos[newIndex]=LitInfo::getOpposite(lInfos[i]);
      lInfos[newIndex].liIndex=newIndex;
    }
    sresLiteral=sresNoLiteral;
  }

  tree->incTimeStamp();
  enterLiteral(tree->getEntryPoint(), clen==0);
}

void ClauseCodeTree::ClauseMatcher::reset()
{
  // Disposing the LitInfos frees every MatchInfo recorded during the search, so this is
  // where a run that accumulated a great many matches pays for them.
  TIME_TRACE("codetree matcher teardown");

  unsigned liCnt=lInfos.size();
  for(unsigned i=0;i<liCnt;i++) {
    lInfos[i].dispose();
  }
  lms.reset();

#if VDEBUG
  ASS_EQ(tree->_clauseMatcherCounter,1);
  tree->_clauseMatcherCounter--;
#endif
}

/**
 * Return next clause matching query or 0 if there is not such
 */
Clause* ClauseCodeTree::ClauseMatcher::next(int& resolvedQueryLit)
{
  if(lms.isEmpty()) {
    return 0;
  }

  for(;;) {
    LiteralMatcher* lm = &*lms.top();

    //get next literal from the literal matcher
    bool found=lm->next();

    //if there's none, go one level up (or fail if at the top)
    if(!found) {
      leaveLiteral();
      if(lms.isEmpty()) {
	return 0;
      }
    }
    else if(lm->op->isSuccess()) {
      Clause* candidate=lm->op->template getSuccessResult<Clause>();
      RSTAT_MCTR_INC("candidates", lms.size()-1);
      if(checkCandidate(candidate, resolvedQueryLit)) {
	RSTAT_MCTR_INC("candidates (success)", lms.size()-1);
	return candidate;
      }
    }
    else if(canEnterLiteral(lm->op)) {
      ASS(lm->op->isLitEnd());
      ASS_LE(lms.size(), query->length()); //this is due to the seekOnlySuccess part below

      //LIT_END is never the last operation in the CodeBlock,
      //so we can increase here
      CodeOp* newLitEntry=lm->op+1;

      //check that we have cleared the sresLiteral value if it is no longer valid
      ASS(!sres || sresLiteral==sresNoLiteral || sresLiteral<lms.size()-1);

      if(sres && sresLiteral==sresNoLiteral) {
	//we check whether we haven't matched only opposite literals on the previous level
	if(lm->getILS()->noNonOppositeMatches) {
	  sresLiteral=lms.size()-1;
	}
      }

      bool seekOnlySuccess=lms.size()==query->length();
      enterLiteral(newLitEntry, seekOnlySuccess);
    }
  }
}

inline bool ClauseCodeTree::ClauseMatcher::canEnterLiteral(CodeOp* op)
{
  ASS(op->isLitEnd());
  ASS_EQ(lms.top()->op, op);

  ILStruct* ils=op->getILS();
  if(ils->timestamp==tree->_curTimeStamp && ils->visited) {
    return false;
  }

  if(lms.size()>1) {
    //we have already matched and entered some index literals, so we
    //will check for compatibility of variable assignments
    if(ils->varCnt && !lms.top()->eagerlyMatched()) {
      lms.top()->doEagerMatching();
      RSTAT_MST_INC("match count", lms.size()-1, lms.top()->getILS()->matchCnt);
    }
    for(size_t ilIndex=0;ilIndex<lms.size()-1;ilIndex++) {
      ILStruct* prevILS=lms[ilIndex]->getILS();
      if(prevILS->varCnt && !lms[ilIndex]->eagerlyMatched()) {
	lms[ilIndex]->doEagerMatching();
	RSTAT_MST_INC("match count", ilIndex, lms[ilIndex]->getILS()->matchCnt);
      }

      size_t matchIndex=ils->matchCnt;
      while(matchIndex!=0) {
	matchIndex--;
	MatchInfo* mi=ils->getMatch(matchIndex);
	if(!existsCompatibleMatch(ils, mi, prevILS)) {
	  ils->deleteMatch(matchIndex); //decreases ils->matchCnt
	}
      }
      if(!ils->matchCnt) {
	return false;
      }
    }
  }

  return true;
}

/**
 * Enter literal matching starting at @c entry.
 *
 * @param entry the code tree node
 * @param seekOnlySuccess if true, accept only SUCCESS operations
 *   (this is to be used when all literals are matched so we want
 *   to see just clauses that end at this point).
 */
void ClauseCodeTree::ClauseMatcher::enterLiteral(CodeOp* entry, bool seekOnlySuccess)
{
  if(!seekOnlySuccess) {
    RSTAT_MCTR_INC("enterLiteral levels (non-sos)", lms.size());
  }

  if(lms.isNonEmpty()) {
    Recycled<LiteralMatcher, NoReset>& prevLM = lms.top();
    ILStruct* ils=prevLM->op->getILS();
    ASS_EQ(ils->timestamp,tree->_curTimeStamp);
    ASS(!ils->visited);
    ASS(!ils->finished);
    ils->visited=true;
  }

  size_t linfoCnt=lInfos.size();
  if(sres && sresLiteral!=sresNoLiteral) {
    ASS_L(sresLiteral,lms.size());
    //we do not need to match index literals with opposite query
    //literals, as one of already matched index literals matched only
    //to opposite literals (and opposite literals cannot be matched
    //on more than one index literal)
    ASS_EQ(linfoCnt%2,0);
    linfoCnt/=2;
  }

  Recycled<LiteralMatcher, NoReset> lm;
  lm->init(*tree, entry, lInfos.array(), linfoCnt, seekOnlySuccess);
  lms.push(std::move(lm));
}

void ClauseCodeTree::ClauseMatcher::leaveLiteral()
{
  ASS(lms.isNonEmpty());

  lms.pop();

  if(lms.isNonEmpty()) {
    LiteralMatcher* prevLM = &*lms.top();
    ILStruct* ils=prevLM->op->getILS();
    ASS_EQ(ils->timestamp,tree->_curTimeStamp);
    ASS(ils->visited);

    ils->finished=true;

    if(sres) {
      //clear the resolved literal flag if we have backtracked from it
      unsigned depth=lms.size()-1;
      if(sresLiteral==depth) {
        sresLiteral=sresNoLiteral;
      }
      ASS(sresLiteral==sresNoLiteral || sresLiteral<depth);
    }
  }
}


//////////////// Multi-literal matching

bool ClauseCodeTree::ClauseMatcher::checkCandidate(Clause* cl, int& resolvedQueryLit)
{
  unsigned clen=cl->length();
  //the last matcher in mls is the one that yielded the SUCCESS operation
  ASS_EQ(clen, lms.size()-1);
  ASS_EQ(clen, lms[clen-1]->op->getILS()->depth+1);

  if(clen<=1) {
    //if clause doesn't have multiple literals, there is no need
    //for multi-literal matching
    resolvedQueryLit=-1;
    if(sres && clen==1) {
      size_t matchCnt=lms[0]->getILS()->matchCnt;
      for(size_t i=0;i<matchCnt;i++) {
	MatchInfo* mi=lms[0]->getILS()->getMatch(i);
	if(lInfos[mi->liIndex].opposite) {
	  resolvedQueryLit=lInfos[mi->liIndex].litIndex;
	}
	else {
	  //we prefer subsumption to subsumption resolution
	  resolvedQueryLit=-1;
	  break;
	}
      }
    }
    return true;
  }

//  if(matchGlobalVars(resolvedQueryLit)) {
//    return true;
//  }

  // Past this point we are no longer interpreting code-tree ops: the candidate's literals
  // have each been matched individually, and what remains is to find one combination of
  // those matches whose variable bindings agree -- a backtracking search over match
  // vectors (doEagerMatching, then matchGlobalVars/compatible/existsCompatibleMatch),
  // the same kind of work MLMatcher does. Scoped here, above the clen<=1 early exit, so
  // it is entered once per multi-literal candidate and never for a unit one.
  TIME_TRACE("codetree multi-literal matching");

  bool newMatches=false;
  for(int i=clen-1;i>=0;i--) {
    LiteralMatcher* lm = &*lms[i];
    if(lm->eagerlyMatched()) {
      break;
    }
    if(lm->getILS()->varCnt==0) {
      //If the index term is ground, at most two literals can be matched on
      //it (the second one is the opposite one in case we're performing the
      //subsumption resolution) We are here, so we have matched one already,
      //and we know that the query clause doesn't contain two equal or opposite
      //literals (or else it would have been simplified by duplicate literal
      //removal or by tautology deletion). Therefore we don't need to try
      //matching the rest of the query clause.
      continue;
    }
    newMatches|=lm->doEagerMatching();
  }
  (void)newMatches; // to prevent a warning
  return matchGlobalVars(resolvedQueryLit);
//  return newMatches && matchGlobalVars(resolvedQueryLit);
}

bool ClauseCodeTree::ClauseMatcher::matchGlobalVars(int& resolvedQueryLit)
{
  //TODO: perform _set_, not _multiset_ subsumption for subsumption resolution

//  bool verbose=query->number()==58746;
//#define VERB_OUT(x) if(verbose) {cout<<x<<endl;}

  unsigned clen=lms.size()-1;

  //remaining[j,0] contains number of matches for j-th index literal
  //remaining[j,i+1] (for j>i) contains number of matches for j-th
  //  index literal compatible with the bindings of i-th literal (and
  //  those before it)
  //remaining[j,j] therefore contains number of matches we have to try
  //  when we get to binding j-th literal
  //  Matches in ILStruct::matches are reordered, so that we always try
  //  the _first_ remaining[j,j] literals
  static TriangularArray<int> remaining(10);
  remaining.setSide(clen);
  for(unsigned j=0;j<clen;j++) {
    ILStruct* ils=lms[j]->getILS();
    remaining.set(j,0,ils->matchCnt);

//    VERB_OUT("matches "<<ils->matches.size()<<" index:"<<j<<" vars:"<<ils->varCnt<<" linfos:"<<lInfos.size());
//    for(unsigned y=0;y<ils->matches.size();y++) {
//      LitInfo* linf=&lInfos[ils->matches[y]->liIndex];
//      VERB_OUT(" match "<<y<<" liIndex:"<<ils->matches[y]->liIndex<<" op: "<<linf->opposite);
//      VERB_OUT(" hdr: "<<(*linf->ft)[0].number());
//    }
//    for(unsigned x=0;x<ils->varCnt;x++) {
//      VERB_OUT(" glob var: "<<ils->sortedGlobalVarNumbers[x]);
//      for(unsigned y=0;y<ils->matches.size();y++) {
//	VERB_OUT(" match "<<y<<" binding: "<<ils->matches[y]->bindings[x]);
//      }
//    }
  }
//  VERB_OUT("secOp:"<<(lms[1]->op-1)->instr()<<" "<<(lms[1]->op-1)->arg());

  static DArray<int> matchIndex;
  matchIndex.ensure(clen);
  unsigned failLev=0;
  for(unsigned i=0;i<clen;i++) {
    matchIndex[i]=-1;
    if(i>0) { failLev=20; }
  bind_next_match:
    matchIndex[i]++;
    if(matchIndex[i]==remaining.get(i,i)) {
      //no more choices at this level, so try going up
      if(i==0) {
	RSTAT_MCTR_INC("zero level fails at", failLev);
	return false;
      }
      i--;
      goto bind_next_match;
    }
    ASS_L(matchIndex[i],remaining.get(i,i));

    ILStruct* bi=lms[i]->getILS(); 		//bound index literal
    MatchInfo* bq=bi->getMatch(matchIndex[i]);	//bound query literal

    //propagate the implications of this binding to next literals
    for(unsigned j=i+1;j<clen;j++) {
      ILStruct* ni=lms[j]->getILS();		//next index literal
      unsigned rem=remaining.get(j,i);
      unsigned k=0;
      while(k<rem) {
	MatchInfo* nq=ni->getMatch(k);		//next query literal
	if(!compatible(bi,bq,ni,nq)) {
	  rem--;
	  swap(ni->getMatch(k),ni->getMatch(rem));
	  continue;
	}
	k++;
      }
      if(rem==0) {
	if(failLev<j) { failLev=j; }
	goto bind_next_match;
      }
      remaining.set(j,i+1,rem);
    }
  }

  resolvedQueryLit=-1;
  if(sres) {
    for(unsigned i=0;i<clen;i++) {
      ILStruct* ils=lms[i]->getILS();
      MatchInfo* mi=ils->getMatch(matchIndex[i]);
      if(lInfos[mi->liIndex].opposite) {
	resolvedQueryLit=lInfos[mi->liIndex].litIndex;
	break;
      }
    }
  }

  return true;
}

bool ClauseCodeTree::ClauseMatcher::compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq)
{
  if( lInfos[bq->liIndex].litIndex==lInfos[nq->liIndex].litIndex ||
      (lInfos[bq->liIndex].opposite && lInfos[nq->liIndex].opposite) ) {
    return false;
  }

  unsigned bvars=bi->varCnt;
  unsigned* bgvn=bi->sortedGlobalVarNumbers;
  TermList* bb=bq->bindings();

  unsigned nvars=ni->varCnt;
  unsigned* ngvn=ni->sortedGlobalVarNumbers;
  TermList* nb=nq->bindings();

  while(bvars && nvars) {
    while(bvars && *bgvn<*ngvn) {
      bvars--;
      bgvn++;
      bb++;
    }
    if(!bvars) {
      break;
    }
    while(nvars && *bgvn>*ngvn) {
      nvars--;
      ngvn++;
      nb++;
    }
    while(bvars && nvars && *bgvn==*ngvn) {
      if(*bb!=*nb) {
	return false;
      }
      bvars--;
      bgvn++;
      bb++;
      nvars--;
      ngvn++;
      nb++;
    }
  }

  return true;
}

bool ClauseCodeTree::ClauseMatcher::existsCompatibleMatch(ILStruct* si, MatchInfo* sq, ILStruct* targets)
{
  size_t tcnt=targets->matchCnt;
  for(size_t i=0;i<tcnt;i++) {
    if(compatible(si,sq,targets,targets->getMatch(i))) {
      return true;
    }
  }
  return false;
}

}
