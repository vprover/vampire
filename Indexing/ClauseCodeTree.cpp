/**
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include <utility>
 
#include "../Lib/BitUtils.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Sort.hpp"
#include "../Lib/TimeCounter.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/FlatTerm.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#include "ClauseCodeTree.hpp"

#define LOG_OP(x)
//#define LOG_OP(x) cout<<x<<endl
//#define LOG_OP(x) if(TimeCounter::isBeingMeasured(TC_FORWARD_SUBSUMPTION)) { cout<<x<<endl; }

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

//////////////// general datastructures ////////////////////

ClauseCodeTree::LitInfo::LitInfo(Clause* cl, unsigned litIndex)
: litIndex(litIndex), reversed(false), opposite(false)
{
  CALL("ClauseCodeTree::LitInfo::LitInfo");

  ft=FlatTerm::create((*cl)[litIndex]);
}

void ClauseCodeTree::LitInfo::dispose()
{
  ft->destroy();
}

ClauseCodeTree::LitInfo ClauseCodeTree::LitInfo::getReversed(const LitInfo& li)
{
  FlatTerm* ft=FlatTerm::copy(li.ft);
  ft->swapCommutativePredicateArguments();

  LitInfo res=li;
  res.ft=ft;
  return res;
}


ClauseCodeTree::MatchInfo::MatchInfo(ILStruct* ils, unsigned liIndex, DArray<TermList>& bindingArray)
: liIndex(liIndex), bindCnt(ils->varCnt)
{
  if(bindCnt) {
    size_t bSize=sizeof(TermList)*bindCnt;
    bindings=static_cast<TermList*>(
	ALLOC_KNOWN(bSize, "ClauseCodeTree::MatchInfo::bindings"));
	
    unsigned* perm=ils->globalVarPermutation;
    for(unsigned i=0;i<bindCnt;i++) {
      bindings[perm[i]]=bindingArray[i];
    }
  }
  else {
    bindings=0;
  }
}

ClauseCodeTree::MatchInfo::~MatchInfo()
{
  if(bindings) {
    DEALLOC_KNOWN(bindings, sizeof(TermList)*bindCnt, 
		"ClauseCodeTree::MatchInfo::bindings");
  }
}


ClauseCodeTree::ILStruct::ILStruct(unsigned varCnt, Stack<unsigned>& gvnStack)
: varCnt(varCnt), sortedGlobalVarNumbers(0), globalVarPermutation(0), timestamp(0)
{
  if(varCnt) {
    size_t gvnSize=sizeof(unsigned)*varCnt;
    globalVarNumbers=static_cast<unsigned*>(
	ALLOC_KNOWN(gvnSize, "ClauseCodeTree::ILStruct::globalVarNumbers"));
    memcpy(globalVarNumbers, gvnStack.begin(), gvnSize);
  }
  else {
    globalVarNumbers=0;
  }
}

ClauseCodeTree::ILStruct::~ILStruct()
{
  if(globalVarNumbers) {
    size_t gvSize=sizeof(unsigned)*varCnt;
    DEALLOC_KNOWN(globalVarNumbers, gvSize, 
		"ClauseCodeTree::ILStruct::globalVarNumbers");
    if(sortedGlobalVarNumbers) {
      DEALLOC_KNOWN(sortedGlobalVarNumbers, gvSize, 
		  "ClauseCodeTree::ILStruct::sortedGlobalVarNumbers");
    }
    if(globalVarPermutation) {
      DEALLOC_KNOWN(globalVarPermutation, gvSize, 
		  "ClauseCodeTree::ILStruct::globalVarPermutation");
    }
  }

  disposeMatches();
}

/**
 * Comparator used by the @b putIntoSequence function to order global 
 * variable numbers
 */
struct ClauseCodeTree::ILStruct::GVArrComparator
{
  Comparison compare(const pair<unsigned,unsigned>& p1, 
      const pair<unsigned,unsigned>& p2)
  {
    return Int::compare(p1.first, p2.first);
  }
};

/**
 * This function is called by the buildBlock function to make the 
 * ILStruct object relate to its predecessors
 */
void ClauseCodeTree::ILStruct::putIntoSequence(ILStruct* previous_)
{
  CALL("ClauseCodeTree::ILStruct::putIntoSequence");
  
  previous=previous_;
  depth=previous ? (previous->depth+1) : 0;
  
  if(!varCnt) { return; }

  static DArray<pair<unsigned,unsigned> > gvArr;
  gvArr.ensure(varCnt);
  for(unsigned i=0;i<varCnt;i++) {
    gvArr[i].first=globalVarNumbers[i];
    gvArr[i].second=i;
  }
  gvArr.sort(GVArrComparator());

  size_t gvSize=sizeof(unsigned)*varCnt;
  sortedGlobalVarNumbers=static_cast<unsigned*>(
	ALLOC_KNOWN(gvSize, "ClauseCodeTree::ILStruct::sortedGlobalVarNumbers"));
  globalVarPermutation=static_cast<unsigned*>(
	ALLOC_KNOWN(gvSize, "ClauseCodeTree::ILStruct::globalVarPermutation"));
  
  for(unsigned i=0;i<varCnt;i++) {
    sortedGlobalVarNumbers[i]=gvArr[i].first;
    globalVarPermutation[gvArr[i].second]=i;
  }
}

bool ClauseCodeTree::ILStruct::equalsForOpMatching(const ILStruct& o) const
{
  CALL("ClauseCodeTree::ILStruct::equalsForOpMatching");

  if(varCnt!=o.varCnt) {
    return false;
  }
  size_t gvnSize=sizeof(unsigned)*varCnt;
  return BitUtils::memEqual(globalVarNumbers, o.globalVarNumbers, gvnSize);
}

void ClauseCodeTree::ILStruct::disposeMatches()
{
  CALL("ClauseCodeTree::ILStruct::disposeMatches");
  
  while(matches.isNonEmpty()) {
    delete matches.pop();
  }
}


ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getSuccess(Clause* cl)
{
  CALL("ClauseCodeTree::OpCode::getSuccess");
  ASS(cl); //cl has to be a non-zero pointer

  OpCode res;
  res.alternative=0;
  res.result=cl;
  ASS(res.isSuccess());
  return res;
}
ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getLitEnd(ILStruct* ils)
{
  CALL("ClauseCodeTree::OpCode::getLitEnd");

  OpCode res;
  res.alternative=0;
  res.data=reinterpret_cast<size_t>(ils)|LIT_END;
  ASS(res.isLitEnd());
  return res;
}
ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getTermOp(Instruction i, unsigned num)
{
  CALL("ClauseCodeTree::OpCode::getCheckOp");
  ASS(i==CHECK_FUN || i==CHECK_VAR || i==ASSIGN_VAR);

  OpCode res;
  res.alternative=0;
  res.info.instr=i;
  res.info.arg=num;
  return res;
}

/**
 * Return true iff @b o is equal to the object for the purpose
 * of operation matching during cide insertion into the tree
 */
bool ClauseCodeTree::OpCode::equalsForOpMatching(const OpCode& o) const
{
  CALL("ClauseCodeTree::OpCode::equalsForOpMatching");

  if(isLitEnd() && o.isLitEnd()) {
    return getILS()->equalsForOpMatching(*o.getILS());
  }
  
  if(instr()!=o.instr()) {
    return false;
  }
  switch(instr()) {
  case SUCCESS_OR_FAIL:
  case SUCCESS2:
    return data==o.data;
  case CHECK_FUN:
  case CHECK_VAR:
  case ASSIGN_VAR:
    return arg()==o.arg();
  case LIT_END:
  case LIT_END2:
  case SEARCH_STRUCT:
    //SEARCH_STRUCT operations in the tree should be handled separately
    //during insertion into the code tree
    ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

ClauseCodeTree::SearchStruct* ClauseCodeTree::OpCode::getSearchStruct()
{
  CALL("ClauseCodeTree::OpCode::getSearchStruct");
  
  //the following line gives warning for not being according
  //to the standard, so we have to work around
//  static const size_t opOfs=offsetof(SearchStruct,landingOp);
  static const size_t opOfs=reinterpret_cast<size_t>(
	&reinterpret_cast<SearchStruct*>(8)->landingOp)-8;

  SearchStruct* res=reinterpret_cast<SearchStruct*>(
      reinterpret_cast<size_t>(this)-opOfs);
  ASS_ALLOC_TYPE(res,"ClauseCodeTree::SearchStruct");
  return res;
}


ClauseCodeTree::SearchStruct::SearchStruct(size_t length)
: length(length)
{
  CALL("ClauseCodeTree::SearchStruct::SearchStruct");
  ASS(length);
  
  landingOp.alternative=0;
  landingOp.setInstr(SEARCH_STRUCT);
  
  size_t valSize=sizeof(unsigned)*length;
  values=static_cast<unsigned*>(
      ALLOC_KNOWN(valSize, "ClauseCodeTree::SearchStruct::values"));
  size_t tgtSize=sizeof(OpCode*)*length;
  targets=static_cast<OpCode**>(
      ALLOC_KNOWN(tgtSize, "ClauseCodeTree::SearchStruct::targets"));
}

ClauseCodeTree::SearchStruct::~SearchStruct()
{
  CALL("ClauseCodeTree::SearchStruct::~SearchStruct");

  size_t valSize=sizeof(unsigned)*length;
  DEALLOC_KNOWN(values, valSize, "ClauseCodeTree::SearchStruct::values");
  size_t tgtSize=sizeof(OpCode*)*length;
  DEALLOC_KNOWN(targets, tgtSize, "ClauseCodeTree::SearchStruct::targets");
}

ClauseCodeTree::OpCode*& ClauseCodeTree::SearchStruct::targetOp(unsigned fn)
{
  CALL("ClauseCodeTree::SearchStruct::findTargetOp");
  
  size_t left=0;
  size_t right=length-1;
  while(left<right) {
    size_t mid=(left+right)/2;
    switch(Int::compare(fn, values[mid])) {
    case LESS:
      right=mid;
      break;
    case GREATER:
      left=mid+1;
      break;
    case EQUAL:
      return targets[mid];
    }
  }
  ASS_EQ(left,right);
  ASS(left==length-1 || fn<=values[left]);
  return targets[left];
//  if(fn>values[left]) {
//    return &targets[length];
//  }
//  else {
//    return &targets[left];
//  }
}

/**
 * Comparator that compares two CHECK_FUN operations for the 
 * purpose of insertion into the SearchStruct.
 * 
 * Is used in the @b compressCheckFnOps function.
 */
struct ClauseCodeTree::SearchStruct::OpComparator
{
  static Comparison compare(OpCode* op1, OpCode* op2)
  {
    return Int::compare(op1->arg(), op2->arg());
  }
};

//////////////// auxiliary ////////////////////

ClauseCodeTree::ClauseCodeTree()
: _curTimeStamp(0), _maxVarCnt(0), _entryPoint(0)
{
#if VDEBUG
  _clauseMatcherCounter=0;
#endif
}

void ClauseCodeTree::handleClause(Clause* cl, bool adding)
{
  CALL("ClauseCodeTree::handleClause");
  
  TimeCounter tc(TC_FORWARD_SUBSUMPTION_INDEX_MAINTENANCE);

  if(adding) {
    insert(cl);
  }
  else {
    remove(cl);
  }
}

/**
 * Return CodeBlock which contains @b op as its first operation
 */
ClauseCodeTree::CodeBlock* ClauseCodeTree::firstOpToCodeBlock(OpCode* op)
{
  CALL("ClauseCodeTree::firstOpToCodeBlock");

  //the following line gives warning for not being according
  //to the standard, so we have to work around
//  static const size_t opOfs=offsetof(CodeBlock,_array);
  static const size_t opOfs=reinterpret_cast<size_t>(
	&reinterpret_cast<CodeBlock*>(8)->_array[0])-8;

  CodeBlock* res=reinterpret_cast<CodeBlock*>(
      reinterpret_cast<size_t>(op)-opOfs);
  ASS_ALLOC_TYPE(res,"Vector");
  return res;
}


template<class Visitor>
void ClauseCodeTree::visitAllOps(Visitor visitor)
{
  CALL("ClauseCodeTree::visitAllOps");

  static Stack<CodeBlock*> blocks;
  blocks.reset();

  if(_entryPoint) { blocks.push(_entryPoint); }

  while(blocks.isNonEmpty()) {
    CodeBlock* cb=blocks.pop();

    OpCode* op=&(*cb)[0];
    for(size_t rem=cb->length(); rem; rem--,op++) {
	visitor(op);
	if(op->alternative) {
	  blocks.push(firstOpToCodeBlock(op->alternative));
	}
    }
  }
}


//////////////// insertion ////////////////////

void ClauseCodeTree::CompileContext::init()
{
  CALL("ClauseCodeTree::CompileContext::init");

  nextVarNum=0;
  varMap.reset();
  nextGlobalVarNum=0;
  globalVarMap.reset();
}

void ClauseCodeTree::CompileContext::nextLit()
{
  CALL("ClauseCodeTree::CompileContext::nextLit");

  nextVarNum=0;
  varMap.reset();
}

void ClauseCodeTree::CompileContext::deinit(ClauseCodeTree* tree, bool discarded)
{
  CALL("ClauseCodeTree::CompileContext::deinit");

  //update the max. number of variables, if necessary
  if(!discarded && nextGlobalVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextGlobalVarNum;
  }
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

  compileLiteral(lit, code, cctx, false);

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
	  treeOp=ss->targetOp(code[i].arg());
	  continue;
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


void ClauseCodeTree::compileLiteral(Literal* lit, CodeStack& code, CompileContext& cctx, bool addLitEnd)
{
  CALL("ClauseCodeTree::compileLiteral");

  static Stack<unsigned> globalCounterparts;
  globalCounterparts.reset();

  cctx.nextLit();

  code.push(OpCode::getTermOp(CHECK_FUN, lit->header()));

  SubtermIterator sti(lit);

  while(sti.hasNext()) {
    TermList s=sti.next();
    if(s.isVar()) {
      unsigned var=s.var();
      unsigned* varNumPtr;
      if(cctx.varMap.getValuePtr(var,varNumPtr)) {
	*varNumPtr=cctx.nextVarNum++;
	code.push(OpCode::getTermOp(ASSIGN_VAR, *varNumPtr));

	if(addLitEnd) {
	  unsigned* globalVarNumPtr;
	  if(cctx.globalVarMap.getValuePtr(var,globalVarNumPtr)) {
	    *globalVarNumPtr=cctx.nextGlobalVarNum++;
	  }
	  globalCounterparts.push(*globalVarNumPtr);
	}
      }
      else {
	code.push(OpCode::getTermOp(CHECK_VAR, *varNumPtr));
      }
    }
    else {
      ASS(s.isTerm());
      code.push(OpCode::getTermOp(CHECK_FUN, s.term()->functor()));
    }
  }

  if(addLitEnd) {
    unsigned varCnt=cctx.nextVarNum;
    ASS_EQ(varCnt, globalCounterparts.size());
    ILStruct* ils=new ILStruct(varCnt, globalCounterparts);
    code.push(OpCode::getLitEnd(ils));
  }

}

/**
 * Build CodeBlock object from the last @b cnt instructions on the
 * @b code stack.
 *
 * In this function is also set the value for the @b ILStruct::previous
 * members.
 */
ClauseCodeTree::CodeBlock* ClauseCodeTree::buildBlock(CodeStack& code, size_t cnt, ILStruct* prev)
{
  CALL("ClauseCodeTree::buildBlock");

  size_t clen=code.length();
  ASS_LE(cnt,clen);

  CodeBlock* res=CodeBlock::allocate(cnt);
  size_t sOfs=clen-cnt;
  for(size_t i=0;i<cnt;i++) {
    OpCode& op=code[i+sOfs];
    ASS_EQ(op.alternative,0); //the ops should not have an alternattive set yet
    if(op.isLitEnd()) {
      ILStruct* ils=op.getILS();
      ils->putIntoSequence(prev);
      prev=ils;
    }
    (*res)[i]=op;
  }
  return res;
}

/**
 * Incorporate the code in @b code CodeStack into the tree, empty the
 * stack, and make sure all no longer necessary structures are freed.
 */
void ClauseCodeTree::incorporate(CodeStack& code)
{
  CALL("ClauseCodeTree::incorporate");
  ASS(code.top().isSuccess());

  if(isEmpty()) {
    _entryPoint=buildBlock(code, code.length(), 0);
    code.reset();
    return;
  }
  
  static const unsigned checkFunOpThreshold=2; //must be greater than 1 or it would cause loops

  size_t clen=code.length();
  OpCode** tailTarget;
  size_t matchedCnt;
  ILStruct* lastMatchedILS=0;
  
  {
    OpCode* treeOp=getEntryPoint();
    
    for(size_t i=0;i<clen;i++) {
      OpCode* chainStart=treeOp;
      size_t checkFunOps=0;
      for(;;) {
	if(treeOp->isSearchStruct()) {
	  if(code[i].isCheckFun()) {
	    SearchStruct* ss=treeOp->getSearchStruct();
	    OpCode** to=&ss->targetOp(code[i].arg());
	    if(!*to) {
	      tailTarget=to;
	      matchedCnt=i;
	      goto matching_done;
	    }
	    treeOp=*to;
	    continue;
	  }
	}
	else if(code[i].equalsForOpMatching(*treeOp)) {
	  break;
	}
	if(treeOp->alternative) {
	  treeOp=treeOp->alternative;
	}
	else {
	  tailTarget=&treeOp->alternative;
	  matchedCnt=i;
	  goto matching_done;
	}
	if(treeOp->isCheckFun()) {
	  checkFunOps++;
	  if(checkFunOps>checkFunOpThreshold) {
	    //we put CHECK_FUN ops into the SEARCH_STRUCT op, and 
	    //restart with the chain
	    compressCheckFnOps(chainStart);
	    treeOp=chainStart;
	    checkFunOps=0;
	    continue;
	  }
	}
      }

      if(treeOp->isLitEnd()) {
	lastMatchedILS=treeOp->getILS();
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
    //We matched the whole CodeStack. If we are here, we are inserting an 
    //item multiple times. We will insert it anyway, because later we may 
    //be removing it multiple times as well.
    matchedCnt=clen-1;

    //we need to find where to put it
    while(treeOp->alternative) {
      treeOp=treeOp->alternative;
    }
    tailTarget=&treeOp->alternative;
  }
matching_done:
  
  ASS_L(matchedCnt,clen);

  CodeBlock* rem=buildBlock(code, clen-matchedCnt, lastMatchedILS);
  *tailTarget=&(*rem)[0];
  LOG_OP(rem->toString()<<" incorporated, mismatch caused by "<<code[matchedCnt].toString());

  //truncate the part that was used and thus does not need disposing
  code.truncate(matchedCnt);
  //dispose of the unused code
  while(code.isNonEmpty()) {
    if(code.top().isLitEnd()) {
      delete code.top().getILS();
    }
    code.pop();
  }
}

void ClauseCodeTree::compressCheckFnOps(OpCode* chainStart)
{
  CALL("ClauseCodeTree::compressCheckFnOps");
  ASS(chainStart->alternative);
  
  static Stack<OpCode*> toDo;
  static Stack<OpCode*> chfOps;
  static Stack<OpCode*> otherOps;
  toDo.reset();
  chfOps.reset();
  otherOps.reset();
  
  toDo.push(chainStart->alternative);
  while(toDo.isNonEmpty()) {
    OpCode* op=toDo.pop();
    if(op->alternative) {
      toDo.push(op->alternative);
    }
    if(op->isCheckFun()) {
      chfOps.push(op);
    }
    else if(op->isSearchStruct()) {
      SearchStruct* ss=op->getSearchStruct();
      for(size_t i=0;i<ss->length;i++) {
	if(ss->targets[i]) {
	  toDo.push(ss->targets[i]);
	}
      }
      delete ss;
    }
    else {
      otherOps.push(op);
    }
  }

  ASS_G(chfOps.size(),1);
  size_t slen=chfOps.size();
  SearchStruct* res=new SearchStruct(slen);
  
  sort<SearchStruct::OpComparator>(chfOps.begin(), chfOps.end());
  
  for(size_t i=0;i<slen;i++) {
    ASS(chfOps[i]->isCheckFun());
    res->values[i]=chfOps[i]->arg();
    res->targets[i]=chfOps[i];
    chfOps[i]->alternative=0;
  }
  
  OpCode* op=&res->landingOp;
  chainStart->alternative=op;
  while(otherOps.isNonEmpty()) {
    op->alternative=otherOps.pop();
    op=op->alternative;
  }
  op->alternative=0;
}

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
    compileLiteral(lits[i], code, cctx, true);
  }
  code.push(OpCode::getSuccess(cl));

  cctx.deinit(this);

  incorporate(code);
  ASS(code.isEmpty());
}


//////////////// removal ////////////////////

void ClauseCodeTree::remove(Clause* cl)
{
  CALL("ClauseCodeTree::remove");
  
  static ClauseMatcher cm;
  cm.init(this, cl);
  
  Clause* stored;
  do {
    stored=cm.next();
    if(!stored) {
      ASSERTION_VIOLATION;
      INVALID_OPERATION("clause to be removed not found.");
    }
  } while(stored!=cl);
  
  ASS(cm.matched());
  OpCode* successOp=cm.getSuccessOp();
  ASS_EQ(successOp->getSuccessResult(),cl);
  
  successOp->makeFail();
  
  cm.deinit();
}


//////////////// retrieval ////////////////////

ClauseIterator ClauseCodeTree::getSubsumingClauses(Clause* cl)
{
  CALL("ClauseCodeTree::getSubsumingClauses");
  
  if(isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  return vi( new SubsumingClauseIterator(this, cl) );
}

void ClauseCodeTree::incTimeStamp()
{
  _curTimeStamp++;
  if(!_curTimeStamp) {
    //handle overflow
    NOT_IMPLEMENTED;
  }
}

void ClauseCodeTree::LiteralMatcher::init(ClauseCodeTree* tree_, OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_)
{
  CALL("ClauseCodeTree::LiteralMatcher::init");
  ASS_G(linfoCnt_,0);

  tree=tree_;
  entry=entry_;
  linfos=linfos_;
  linfoCnt=linfoCnt_;

  _fresh=true;
  _matched=false;
  _eagerlyMatched=false;
  curLInfo=0;
  btStack.reset();
  bindings.ensure(tree->_maxVarCnt);
  eagerResults.reset();

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
  ASS(btStack.isEmpty()); //there are no other alternatives now
  ASS_EQ(curLInfo,linfoCnt);
  //we want to yield SUCCESS operations first (as after them there may 
  //be no need for further clause retrieval)
  while(successes.isNonEmpty()) {
    eagerResults.push(successes.pop());
  }
  
  _eagerlyMatched=true;

#if VDEBUG
  //now the context for the tree code execution is invalid
  bindings.ensure(0);
  ft=0;
  curLInfo=-1;
  tp=-1;
#endif

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

bool ClauseCodeTree::LiteralMatcher::execute()
{
  CALL("ClauseCodeTree::LiteralMatcher::execute");
  ASS_L(curLInfo,linfoCnt); //we haven't finished yet

  if(_fresh) {
    _fresh=false;
  }
  else {
    //we backtrack from what we found in the previous run
    if(!backtrack()) {
      return false;
    }
  }


  bool shouldBacktrack=false;
  for(;;) {
    if(op->alternative) {
      LOG_OP("alt at "<<tp);
      btStack.push(BTPoint(tp, op->alternative));
    }
    LOG_OP(tp<<':'<<op->instr());
    switch(op->instr()) {
    case CHECK_FUN:
      shouldBacktrack=!doCheckFun();
      break;
    case ASSIGN_VAR:
      doAssignVar();
      break;
    case CHECK_VAR:
      shouldBacktrack=!doCheckVar();
      break;
    case SEARCH_STRUCT:
      if(doSearchStruct()) {
	//a new value of @b op is assigned, so restart the loop
	continue;
      }
      else {
	shouldBacktrack=true;
      }
      break;
    case LIT_END:
    case LIT_END2:
      return true;
    case SUCCESS_OR_FAIL:
      if(op->isFail()) {
	shouldBacktrack=true;
	break;
      }
    case SUCCESS2:
      //SUCCESS can only appear as the first operation in a literal block
      ASS_EQ(tp,0);
      //yield successes only in the first round (we don't want to yield the
      //same thing for each query literal)
      if(curLInfo==0) {
	return true;
      }
      else {
	shouldBacktrack=true;
      }
      break;
    }
    if(shouldBacktrack) {
      if(!backtrack()) {
	LOG_OP("not found");
	return false;
      }
      LOG_OP(ctx.tp<<"<-bt");
      shouldBacktrack=false;
    }
    else {
      //the SEARCH_STRUCT operation does not appear in CodeBlocks
      ASS(!op->isSearchStruct());
      //In each CodeBlock there is always either operation LIT_END or FAIL.
      //As we haven't encountered one yet, we may safely increase the
      //operation pointer
      op++;
    }
  }
}

bool ClauseCodeTree::LiteralMatcher::backtrack()
{
  if(btStack.isEmpty()) {
    curLInfo++;
    return prepareLiteral();
  }
  BTPoint bp=btStack.pop();
  tp=bp.tp;
  op=bp.op;
  return true;
}

bool ClauseCodeTree::LiteralMatcher::prepareLiteral()
{
  CALL("ClauseCodeTree::LiteralMatcher::prepareLiteral");
  ASS_LE(curLInfo,linfoCnt);

  if(curLInfo==linfoCnt) {
    return false;
  }
  ASS_L(curLInfo,linfoCnt);
  tp=0;
  op=entry;
  ft=linfos[curLInfo].ft;
  return true;
}

inline bool ClauseCodeTree::LiteralMatcher::doSearchStruct()
{
  ASS_EQ(op->instr(), SEARCH_STRUCT);

  const FlatTerm::Entry& fte=(*ft)[tp];
  if(!fte.isFun()) {
    return false;
  }
  op=op->getSearchStruct()->targetOp(fte.number());
  return true;
}

inline bool ClauseCodeTree::LiteralMatcher::doCheckFun()
{
  ASS_EQ(op->instr(), CHECK_FUN);

  unsigned functor=op->arg();
  const FlatTerm::Entry& fte=(*ft)[tp];
  if(!fte.isFun(functor)) {
    return false;
  }
  tp+=FlatTerm::functionEntryCount;
  return true;
}

inline void ClauseCodeTree::LiteralMatcher::doAssignVar()
{
  ASS_EQ(op->instr(), ASSIGN_VAR);

  unsigned var=op->arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(fte->tag()==FlatTerm::VAR) {
    bindings[var]=TermList(fte->number(),false);
    tp++;
  }
  else {
    ASS_EQ(fte->tag(), FlatTerm::FUN);
    fte++;
    ASS_EQ(fte->tag(), FlatTerm::FUN_TERM_PTR);
    ASS(fte->ptr());
    bindings[var]=TermList(fte->ptr());
    fte++;
    ASS_EQ(fte->tag(), FlatTerm::FUN_RIGHT_OFS);
    tp+=fte->number();
  }
}

inline bool ClauseCodeTree::LiteralMatcher::doCheckVar()
{
  ASS_EQ(op->instr(), CHECK_VAR);

  unsigned var=op->arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(fte->tag()==FlatTerm::VAR) {
    if(bindings[var]!=TermList(fte->number(),false)) {
      return false;
    }
    tp++;
  }
  else {
    ASS_EQ(fte->tag(), FlatTerm::FUN);
    fte++;
    ASS_EQ(fte->tag(), FlatTerm::FUN_TERM_PTR);
    if(bindings[var]!=TermList(fte->ptr())) {
      return false;
    }
    fte++;
    ASS_EQ(fte->tag(), FlatTerm::FUN_RIGHT_OFS);
    tp+=fte->number();
  }
  return true;
}

////////// ClauseMatcher

/**
 * Initialize the ClauseMatcher to retrieve generalizetions
 * of the @b query_ clause
 */
void ClauseCodeTree::ClauseMatcher::init(ClauseCodeTree* tree_, Clause* query_)
{
  CALL("ClauseCodeTree::ClauseMatcher::init");
  ASS(!tree_->isEmpty());
  
  query=query_;
  tree=tree_;
  lms.reset();

#if VDEBUG
  ASS_EQ(tree->_clauseMatcherCounter,0);
  tree->_clauseMatcherCounter++;
#endif
  
  //init LitInfo records
  unsigned clen=query->length();
  unsigned liCnt=clen;
  for(unsigned i=0;i<clen;i++) {
    if((*query)[i]->isEquality()) {
      liCnt++;
    }
  }
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

  tree->incTimeStamp();
  enterLiteral(tree->getEntryPoint());
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
Clause* ClauseCodeTree::ClauseMatcher::next()
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
      Clause* candidate=lm->op->getSuccessResult();
      if(checkCandidate(candidate)) {
	return candidate;
      }
    }
    else if(!litEndAlreadyVisited(lm->op)) {
      //LIT_END is never the last operation in the CodeBlock, 
      //so we can increase here
      OpCode* newLitEntry=lm->op+1;
      enterLiteral(newLitEntry);
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

void ClauseCodeTree::ClauseMatcher::enterLiteral(OpCode* entry)
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
  
  LiteralMatcher* lm;
  Recycler::get(lm);
  lm->init(tree, entry, lInfos.array(), lInfos.size());
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
  }
}


//////////////// Multi-literal matching /////////

bool ClauseCodeTree::ClauseMatcher::checkCandidate(Clause* cl)
{
  CALL("ClauseCodeTree::ClauseMatcher::checkCandidate");
  
//  bool verbose=false;//cl->number()==784 && query->number()==1053;
//#define VERB_OUT(x) if(verbose) {cout<<x<<endl;}
  
  unsigned clen=cl->length();
  //the last matcher in mls is the one that yielded the SUCCESS operation
  ASS_EQ(clen, lms.size()-1);
  ASS_EQ(clen, lms[clen-1]->op->getILS()->depth+1);
  
  if(clen<=1) {
    //if clause doesn't have multiple literals, there is no need 
    //for multi-literal matching
    return true;
  }

//  if(matchGlobalVars()) {
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
  
  return matchGlobalVars();
//  return newMatches && matchGlobalVars();
}

bool ClauseCodeTree::ClauseMatcher::matchGlobalVars()
{
  CALL("ClauseCodeTree::ClauseMatcher::matchGlobalVars");
  
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
//    VERB_OUT("matches "<<ils->matches.size()<<" index:"<<j<<" vars:"<<ils->varCnt);
//    for(unsigned x=0;x<ils->varCnt;x++) {
//      VERB_OUT(" glob var: "<<ils->sortedGlobalVarNumbers[x]);
//      for(unsigned y=0;y<ils->matches.size();y++) {
//	VERB_OUT(" match "<<y<<" binding: "<<ils->matches[y]->bindings[x]);
//      }
//    }
  }
  
  static DArray<int> matchIndex;
  matchIndex.ensure(clen);
  for(unsigned i=0;i<clen;i++) {
    matchIndex[i]=-1;
  bind_next_match:
    matchIndex[i]++;
    if(matchIndex[i]==remaining.get(i,i)) {
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









































