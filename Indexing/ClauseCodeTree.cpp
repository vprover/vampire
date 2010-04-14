/**
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include <utility>
 
#include "../Lib/BitUtils.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Recycler.hpp"
#include "../Lib/Sort.hpp"
#include "../Lib/TriangularArray.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/FlatTerm.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#include "ClauseCodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

ClauseCodeTree::ClauseCodeTree()
{
  _clauseCodeTree=true;
#if VDEBUG
  _clauseMatcherCounter=0;
#endif
}

//////////////// insertion ////////////////////

void ClauseCodeTree::insert(Clause* cl)
{
  CALL("ClauseCodeTree::insert");

  unsigned clen=cl->length();
  static DArray<Literal*> lits;
  lits.initFromArray(clen, *cl);

  optimizeLiteralOrder(lits);

  static CodeStack code;
  code.reset();

  static CompileContext cctx;
  cctx.init();

  for(unsigned i=0;i<clen;i++) {
    compileTerm(lits[i], code, cctx, true);
  }
  code.push(OpCode::getSuccess(cl));

  cctx.deinit(this);

  incorporate(code);
  ASS(code.isEmpty());
}

void ClauseCodeTree::optimizeLiteralOrder(DArray<Literal*>& lits)
{
  CALL("ClauseCodeTree::optimizeLiteralOrder");

  unsigned clen=lits.size();
  if(!isEmpty() && clen>1) {

    size_t aux;

    unsigned bestIndex=0;
    size_t bestSharedLen;
    evalSharing(lits[0], getEntryPoint(), bestSharedLen, aux);

    for(unsigned i=0;i<clen;i++) {
      size_t sharedLen;
      evalSharing(lits[i], getEntryPoint(), sharedLen, aux);
      if(sharedLen>bestSharedLen) {
//	cout<<lits[i]->toString()<<" is better than "<<lits[bestIndex]->toString()<<endl;
	bestSharedLen=sharedLen;
	bestIndex=i;
      }
    }
    swap(lits[0],lits[bestIndex]);
  }
}

void ClauseCodeTree::evalSharing(Literal* lit, OpCode* startOp, size_t& sharedLen, size_t& unsharedLen)
{
  CALL("ClauseCodeTree::evalSharing");

  static CodeStack code;
  static CompileContext cctx;

  code.reset();
  cctx.init();

  compileTerm(lit, code, cctx, false);

  cctx.deinit(this, true);

  matchCode(code, startOp, sharedLen);

  unsharedLen=code.size()-sharedLen;
}

/**
 * Match the operations in @b code CodeStack on the code starting at @b startOp.
 *
 * Into @b matchedCnt assign number of matched operations and into @b lastAttemptedOp
 * the last operation on which we have attempted matching. If @b matchedCnt==code.size(),
 * the @b lastAttemptedOp is equal to the last operation in the @b code stack, otherwise
 * it is the first operation on which mismatch occured and there was no alternative to
 * proceed to (in this case it therefore holds that @b lastAttemptedOp->alternative==0 ).
 */
void ClauseCodeTree::matchCode(CodeStack& code, OpCode* startOp, size_t& matchedCnt)
{
  CALL("ClauseCodeTree::matchCode");

  size_t clen=code.length();
  OpCode* treeOp=startOp;
  
  for(size_t i=0;i<clen;i++) {
    for(;;) {
      if(treeOp->isSearchStruct()) {
	if(code[i].isCheckFun()) {
	  SearchStruct* ss=treeOp->getSearchStruct();
	  OpCode* target=ss->targetOp(code[i].arg());
	  if(target) {
	    treeOp=target;
	    continue;
	  }
	}
      }
      else if(code[i].equalsForOpMatching(*treeOp)) {
	break;
      }
      treeOp=treeOp->alternative;
      if(!treeOp) {
	matchedCnt=i;
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
}


//////////////// removal ////////////////////

void ClauseCodeTree::remove(Clause* cl)
{
  CALL("ClauseCodeTree::remove");

  static DArray<LitInfo> lInfos;
  static Stack<OpCode*> firstsInBlocks;
  static Stack<RemovingLiteralMatcher*> rlms;

  unsigned clen=cl->length();
  lInfos.ensure(clen);
  firstsInBlocks.reset();
  rlms.reset();
  
  if(!clen) {
    OpCode* op=getEntryPoint();
    firstsInBlocks.push(op);
    if(!removeOneOfAlternatives(op, cl, &firstsInBlocks)) {
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

  OpCode* op=getEntryPoint();
  firstsInBlocks.push(op);
  unsigned depth=0;
  for(;;) {
    RemovingLiteralMatcher* rlm;
    Recycler::get(rlm);
    rlm->init(op, lInfos.array(), lInfos.size(), this, &firstsInBlocks);
    rlms.push(rlm);
    
  iteration_restart:
    if(!rlm->next()) {
      if(depth==0) {
	ASSERTION_VIOLATION;
	INVALID_OPERATION("clause to be removed was not found");
      }
      Recycler::release(rlms.pop());
      depth--;
      rlm=rlms.top();
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
      if(removeOneOfAlternatives(op, cl, &firstsInBlocks)) {
	//successfully removed
	break;
      }
      goto iteration_restart;
    }
    ASS_L(depth,clen-1);
    depth++;
  }
  
  while(rlms.isNonEmpty()) {
    Recycler::release(rlms.pop());
  }
  for(unsigned i=0;i<clen;i++) {
    lInfos[i].dispose();
  }
}

void ClauseCodeTree::RemovingLiteralMatcher::init(OpCode* entry_, LitInfo* linfos_,
    size_t linfoCnt_, ClauseCodeTree* tree_, Stack<OpCode*>* firstsInBlocks_)
{
  CALL("ClauseCodeTree::RemovingLiteralMatcher::init");
  
  RemovingMatcher::init(entry_, linfos_, linfoCnt_, tree_, firstsInBlocks_);
  
  ALWAYS(prepareLiteral());
}

/**
 *
 *
 * The first operation of the CodeBlock containing @b op 
 * must already be on the @b firstsInBlocks stack.
 */
bool ClauseCodeTree::removeOneOfAlternatives(OpCode* op, Clause* cl, Stack<OpCode*>* firstsInBlocks)
{
  CALL("ClauseCodeTree::removeOneOfAlternatives");
  
  unsigned initDepth=firstsInBlocks->size();

  while(!op->isSuccess() || op->getSuccessResult()!=cl) {
    op=op->alternative;
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

void ClauseCodeTree::LiteralMatcher::init(CodeTree* tree_, OpCode* entry_, 
	LitInfo* linfos_, size_t linfoCnt_, bool seekOnlySuccess)
{
  CALL("ClauseCodeTree::LiteralMatcher::init");
  ASS_G(linfoCnt_,0);
  
  Matcher::init(tree_,entry_);

  linfos=linfos_;
  linfoCnt=linfoCnt_;

  _eagerlyMatched=false;
  eagerResults.reset();

  if(seekOnlySuccess) {
    //we are interested only in SUCCESS operations
    //(and those must be at the entry point or its alternatives)

    _eagerlyMatched=true;
    _fresh=false;
    OpCode* sop=entry;
    while(sop) {
      if(sop->isSuccess()) {
	eagerResults.push(sop);
      }
      sop=sop->alternative;
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
  CALL("ClauseCodeTree::LiteralMatcher::next");
  
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
 * Perofrm eager matching and return true iff new matches were found
 */
bool ClauseCodeTree::LiteralMatcher::doEagerMatching()
{
  CALL("ClauseCodeTree::LiteralMatcher::doEagerMatching");
  ASS(!eagerlyMatched()); //eager matching can be done only once
  ASS(eagerResults.isEmpty());
  ASS(!finished());
  
  //backup the current op
  OpCode* currOp=op;
  
  static Stack<OpCode*> successes;
  successes.reset();
  
  while(execute()) {
    if(op->isLitEnd()) {
      recordMatch();
      eagerResults.push(op);
    }
    else {
      ASS(op->isSuccess());
      successes.push(op);
    }
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
  CALL("ClauseCodeTree::LiteralMatcher::recordMatch");
  ASS(matched());

  ILStruct* ils=op->getILS();
  if(ils->timestamp!=tree->_curTimeStamp) {
    ils->timestamp=tree->_curTimeStamp;
    ils->disposeMatches();
    ils->visited=false;
    ils->finished=false;
  }
  else if(ils->finished) {
    //no need to record matches which we already know will not lead to anything
    return;
  }
  MatchInfo* mi=new MatchInfo(ils, linfos[curLInfo].liIndex, bindings);
  ils->matches.push(mi);
}


////////// ClauseMatcher

/**
 * Initialize the ClauseMatcher to retrieve generalizetions
 * of the @b query_ clause
 */
void ClauseCodeTree::ClauseMatcher::init(ClauseCodeTree* tree_, Clause* query_, bool sres_)
{
  CALL("ClauseCodeTree::ClauseMatcher::init");
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
  unsigned liIndex=0;
  for(unsigned i=0;i<clen;i++) {
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

void ClauseCodeTree::ClauseMatcher::deinit()
{
  CALL("ClauseCodeTree::ClauseMatcher::deinit");

  unsigned liCnt=lInfos.size();
  for(unsigned i=0;i<liCnt;i++) {
    lInfos[i].dispose();
  }
  while(lms.isNonEmpty()) {
    LiteralMatcher* lm=lms.pop();
    Recycler::release(lm);
  }
  
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
  CALL("ClauseCodeTree::ClauseMatcher::next");

  if(lms.isEmpty()) {
    return 0;
  }
  
  for(;;) {
    LiteralMatcher* lm=lms.top();

    bool found=lm->next();
    
    if(!found) {
      leaveLiteral();
      if(lms.isEmpty()) {
	return 0;
      }
    }
    else if(lm->op->isSuccess()) {
      Clause* candidate=static_cast<Clause*>(lm->op->getSuccessResult());
      if(checkCandidate(candidate, resolvedQueryLit)) {
	return candidate;
      }
    }
    else if(!litEndAlreadyVisited(lm->op)) {
      ASS(lm->op->isLitEnd());
      ASS_LE(lms.size(), query->length()); //this is due to the seekOnlySuccess part below

      //LIT_END is never the last operation in the CodeBlock,
      //so we can increase here
      OpCode* newLitEntry=lm->op+1;

      if(sres && sresLiteral==sresNoLiteral) {
	//we check whether we haven't matched only opposite literals on the previous level
	MatchStack& prevMatches=lm->getILS()->matches;
	if(prevMatches.size() && lInfos[prevMatches[0]->liIndex].opposite) {
	  sresLiteral=lms.size()-1;
#if VDEBUG
	  for(unsigned i=1;i<prevMatches.size();i++) {
	    //liIndex in matches must be ascending
	    ASS_G(prevMatches[i]->liIndex,prevMatches[i-1]->liIndex);
	    //all matches after an opposite match must be opposite as well
	    ASS(lInfos[prevMatches[i]->liIndex].opposite);
	  }
#endif
	}
      }

      bool seekOnlySuccess=lms.size()==query->length();
      enterLiteral(newLitEntry, seekOnlySuccess);
    }
  }
}

inline bool ClauseCodeTree::ClauseMatcher::litEndAlreadyVisited(OpCode* op)
{
  CALL("ClauseCodeTree::ClauseMatcher::litEndAlreadyVisited");
  ASS(op->isLitEnd());
  
  ILStruct* ils=op->getILS();
  return ils->timestamp==tree->_curTimeStamp && ils->visited;
}

void ClauseCodeTree::ClauseMatcher::enterLiteral(OpCode* entry, bool seekOnlySuccess)
{
  CALL("ClauseCodeTree::ClauseMatcher::enterLiteral");
  
  if(lms.isNonEmpty()) {
    LiteralMatcher* prevLM=lms.top();
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

  LiteralMatcher* lm;
  Recycler::get(lm);
  lm->init(tree, entry, lInfos.array(), linfoCnt, seekOnlySuccess);
  lms.push(lm);
}

void ClauseCodeTree::ClauseMatcher::leaveLiteral()
{
  CALL("ClauseCodeTree::ClauseMatcher::leaveLiteral");
  ASS(lms.isNonEmpty());
  
  LiteralMatcher* lm=lms.pop();
  Recycler::release(lm);
  
  if(lms.isNonEmpty()) {
    LiteralMatcher* prevLM=lms.top();
    ILStruct* ils=prevLM->op->getILS();
    ASS_EQ(ils->timestamp,tree->_curTimeStamp);
    ASS(ils->visited);
    
    ils->disposeMatches();
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
  CALL("ClauseCodeTree::ClauseMatcher::checkCandidate");
  
  unsigned clen=cl->length();
  //the last matcher in mls is the one that yielded the SUCCESS operation
  ASS_EQ(clen, lms.size()-1);
  ASS_EQ(clen, lms[clen-1]->op->getILS()->depth+1);
  
  if(clen<=1) {
    //if clause doesn't have multiple literals, there is no need 
    //for multi-literal matching
    resolvedQueryLit=-1;
    if(sres) {
      MatchStack::Iterator mit(lms[clen-1]->getILS()->matches);
      while(mit.hasNext()) {
	MatchInfo* mi=mit.next();
	if(!lInfos[mi->liIndex].opposite) {
	  //we preffer subsumption to subsumption resolution
	  resolvedQueryLit=-1;
	  break;
	}
	else {
	  resolvedQueryLit=lInfos[mi->liIndex].litIndex;
	}
      }
    }
    return true;
  }

//  if(matchGlobalVars(resolvedQueryLit)) {
//    return true;
//  }
  
  bool newMatches=false;
  for(int i=clen-1;i>=0;i--) {
    LiteralMatcher* lm=lms[i];
    if(lm->eagerlyMatched()) {
      break;
    }
    newMatches|=lm->doEagerMatching();
  }
  
  return matchGlobalVars(resolvedQueryLit);
//  return newMatches && matchGlobalVars(resolvedQueryLit);
}

bool ClauseCodeTree::ClauseMatcher::matchGlobalVars(int& resolvedQueryLit)
{
  CALL("ClauseCodeTree::ClauseMatcher::matchGlobalVars");
  
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
    remaining.set(j,0,ils->matches.size());
    
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
  for(unsigned i=0;i<clen;i++) {
    matchIndex[i]=-1;
  bind_next_match:
    matchIndex[i]++;
    if(matchIndex[i]==remaining.get(i,i)) {
      //no more choices at this level, so try going up
      if(i==0) {
	return false;
      }
      i--;
      goto bind_next_match;
    }
    ASS_L(matchIndex[i],remaining.get(i,i));
    
    ILStruct* bi=lms[i]->getILS(); 		//bound index literal
    MatchInfo* bq=bi->matches[matchIndex[i]];	//bound query literal
    
    //propagate the implications of this binding to next literals
    for(unsigned j=i+1;j<clen;j++) {
      ILStruct* ni=lms[j]->getILS();		//next index literal
      unsigned rem=remaining.get(j,i);
      unsigned k=0;
      while(k<rem) {
	MatchInfo* nq=ni->matches[k];		//next query literal
	if(!compatible(bi,bq,ni,nq)) {
	  rem--;
	  swap(ni->matches[k],ni->matches[rem]);
	  continue;
	}
	k++;
      }
      if(rem==0) {
	goto bind_next_match;
      }
      remaining.set(j,i+1,rem);
    }
  }
  
  resolvedQueryLit=-1;
  if(sres) {
    for(unsigned i=0;i<clen;i++) {
      ILStruct* ils=lms[i]->getILS();
      MatchInfo* mi=ils->matches[matchIndex[i]];
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
  CALL("ClauseCodeTree::ClauseMatcher::compatible");
  ASS_L(bi->depth, ni->depth);
  
  if( lInfos[bq->liIndex].litIndex==lInfos[nq->liIndex].litIndex ||
      (lInfos[bq->liIndex].opposite && lInfos[nq->liIndex].opposite) ) {
    return false;
  }
  
  unsigned bvars=bi->varCnt;
  unsigned* bgvn=bi->sortedGlobalVarNumbers;
  TermList* bb=bq->bindings;
  
  unsigned nvars=ni->varCnt;
  unsigned* ngvn=ni->sortedGlobalVarNumbers;
  TermList* nb=nq->bindings;
  
  while(bvars && nvars) {
    while(bvars && *bgvn<*ngvn) {
      bvars--;
      bgvn++;
      bb++;
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

}

