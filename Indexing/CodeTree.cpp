/**
 * @file CodeTree.cpp
 * Implements class CodeTree.
 */

#include <utility>
 
#include "../Lib/BitUtils.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Portability.hpp"
#include "../Lib/Sort.hpp"
#include "../Lib/TimeCounter.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/FlatTerm.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#include "CodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

//////////////// general datastructures ////////////////////

CodeTree::LitInfo::LitInfo(Clause* cl, unsigned litIndex)
: litIndex(litIndex), opposite(false)
{
  CALL("CodeTree::LitInfo::LitInfo");

  ft=FlatTerm::create((*cl)[litIndex]);
}

void CodeTree::LitInfo::dispose()
{
  ft->destroy();
}

CodeTree::LitInfo CodeTree::LitInfo::getReversed(const LitInfo& li)
{
  FlatTerm* ft=FlatTerm::copy(li.ft);
  ft->swapCommutativePredicateArguments();

  LitInfo res=li;
  res.ft=ft;
#if VDEBUG
  res.liIndex=-1; //the liIndex has to be updated by caller
#endif
  return res;
}

CodeTree::LitInfo CodeTree::LitInfo::getOpposite(const LitInfo& li)
{
  FlatTerm* ft=FlatTerm::copy(li.ft);
  ft->changeLiteralPolarity();

  LitInfo res=li;
  res.ft=ft;
  res.opposite=true;
#if VDEBUG
  res.liIndex=-1; //the liIndex has to be updated by caller
#endif
  return res;
}


CodeTree::MatchInfo::MatchInfo(ILStruct* ils, unsigned liIndex, DArray<TermList>& bindingArray)
: liIndex(liIndex), bindCnt(ils->varCnt)
{
  if(bindCnt) {
    size_t bSize=sizeof(TermList)*bindCnt;
    bindings=static_cast<TermList*>(
	ALLOC_KNOWN(bSize, "CodeTree::MatchInfo::bindings"));
	
    unsigned* perm=ils->globalVarPermutation;
    for(unsigned i=0;i<bindCnt;i++) {
      bindings[perm[i]]=bindingArray[i];
    }
  }
  else {
    bindings=0;
  }
}

CodeTree::MatchInfo::~MatchInfo()
{
  if(bindings) {
    DEALLOC_KNOWN(bindings, sizeof(TermList)*bindCnt, 
		"CodeTree::MatchInfo::bindings");
  }
}


CodeTree::ILStruct::ILStruct(unsigned varCnt, Stack<unsigned>& gvnStack)
: varCnt(varCnt), sortedGlobalVarNumbers(0), globalVarPermutation(0), timestamp(0)
{
  if(varCnt) {
    size_t gvnSize=sizeof(unsigned)*varCnt;
    globalVarNumbers=static_cast<unsigned*>(
	ALLOC_KNOWN(gvnSize, "CodeTree::ILStruct::globalVarNumbers"));
    memcpy(globalVarNumbers, gvnStack.begin(), gvnSize);
  }
  else {
    globalVarNumbers=0;
  }
}

CodeTree::ILStruct::~ILStruct()
{
  disposeMatches();
  
  if(globalVarNumbers) {
    size_t gvSize=sizeof(unsigned)*varCnt;
    DEALLOC_KNOWN(globalVarNumbers, gvSize, 
		"CodeTree::ILStruct::globalVarNumbers");
    if(sortedGlobalVarNumbers) {
      DEALLOC_KNOWN(sortedGlobalVarNumbers, gvSize, 
		  "CodeTree::ILStruct::sortedGlobalVarNumbers");
    }
    if(globalVarPermutation) {
      DEALLOC_KNOWN(globalVarPermutation, gvSize, 
		  "CodeTree::ILStruct::globalVarPermutation");
    }
  }
}

/**
 * Comparator used by the @b putIntoSequence function to order global 
 * variable numbers
 */
struct CodeTree::ILStruct::GVArrComparator
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
void CodeTree::ILStruct::putIntoSequence(ILStruct* previous_)
{
  CALL("CodeTree::ILStruct::putIntoSequence");
  
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
	ALLOC_KNOWN(gvSize, "CodeTree::ILStruct::sortedGlobalVarNumbers"));
  globalVarPermutation=static_cast<unsigned*>(
	ALLOC_KNOWN(gvSize, "CodeTree::ILStruct::globalVarPermutation"));
  
  for(unsigned i=0;i<varCnt;i++) {
    sortedGlobalVarNumbers[i]=gvArr[i].first;
    globalVarPermutation[gvArr[i].second]=i;
  }
}

bool CodeTree::ILStruct::equalsForOpMatching(const ILStruct& o) const
{
  CALL("CodeTree::ILStruct::equalsForOpMatching");

  if(varCnt!=o.varCnt) {
    return false;
  }
  size_t gvnSize=sizeof(unsigned)*varCnt;
  return BitUtils::memEqual(globalVarNumbers, o.globalVarNumbers, gvnSize);
}

void CodeTree::ILStruct::disposeMatches()
{
  CALL("CodeTree::ILStruct::disposeMatches");
  
  while(matches.isNonEmpty()) {
    delete matches.pop();
  }
}


CodeTree::OpCode CodeTree::OpCode::getSuccess(void* data)
{
  CALL("CodeTree::OpCode::getSuccess");
  ASS(data); //data has to be a non-zero pointer

  OpCode res;
  res.alternative=0;
  res.result=data;
  ASS(res.isSuccess());
  return res;
}
CodeTree::OpCode CodeTree::OpCode::getLitEnd(ILStruct* ils)
{
  CALL("CodeTree::OpCode::getLitEnd");

  OpCode res;
  res.alternative=0;
  res.data=reinterpret_cast<size_t>(ils)|LIT_END;
  ASS(res.isLitEnd());
  return res;
}
CodeTree::OpCode CodeTree::OpCode::getTermOp(Instruction i, unsigned num)
{
  CALL("CodeTree::OpCode::getCheckOp");
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
bool CodeTree::OpCode::equalsForOpMatching(const OpCode& o) const
{
  CALL("CodeTree::OpCode::equalsForOpMatching");

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

CodeTree::SearchStruct* CodeTree::OpCode::getSearchStruct()
{
  CALL("CodeTree::OpCode::getSearchStruct");
  
  //the following line gives warning for not being according
  //to the standard, so we have to work around
//  static const size_t opOfs=offsetof(SearchStruct,landingOp);
  static const size_t opOfs=reinterpret_cast<size_t>(
	&reinterpret_cast<SearchStruct*>(8)->landingOp)-8;

  SearchStruct* res=reinterpret_cast<SearchStruct*>(
      reinterpret_cast<size_t>(this)-opOfs);
  ASS_ALLOC_TYPE(res,"CodeTree::SearchStruct");
  return res;
}


CodeTree::SearchStruct::SearchStruct(size_t length)
: length(length)
{
  CALL("CodeTree::SearchStruct::SearchStruct");
  ASS(length);
  
  landingOp.alternative=0;
  landingOp.setInstr(SEARCH_STRUCT);
  
  size_t valSize=sizeof(unsigned)*length;
  values=static_cast<unsigned*>(
      ALLOC_KNOWN(valSize, "CodeTree::SearchStruct::values"));
  size_t tgtSize=sizeof(OpCode*)*length;
  targets=static_cast<OpCode**>(
      ALLOC_KNOWN(tgtSize, "CodeTree::SearchStruct::targets"));
}

CodeTree::SearchStruct::~SearchStruct()
{
  CALL("CodeTree::SearchStruct::~SearchStruct");

  size_t valSize=sizeof(unsigned)*length;
  DEALLOC_KNOWN(values, valSize, "CodeTree::SearchStruct::values");
  size_t tgtSize=sizeof(OpCode*)*length;
  DEALLOC_KNOWN(targets, tgtSize, "CodeTree::SearchStruct::targets");
}

CodeTree::OpCode*& CodeTree::SearchStruct::targetOp(unsigned fn)
{
  CALL("CodeTree::SearchStruct::findTargetOp");
  
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
struct CodeTree::SearchStruct::OpComparator
{
  static Comparison compare(OpCode* op1, OpCode* op2)
  {
    return Int::compare(op1->arg(), op2->arg());
  }
};

//////////////// auxiliary ////////////////////

CodeTree::CodeTree()
: _curTimeStamp(0), _maxVarCnt(1), _entryPoint(0)
{
}

/**
 * Return CodeBlock which contains @b op as its first operation
 */
CodeTree::CodeBlock* CodeTree::firstOpToCodeBlock(OpCode* op)
{
  CALL("CodeTree::firstOpToCodeBlock");
  ASS(!op->isSearchStruct());

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
void CodeTree::visitAllOps(Visitor visitor)
{
  CALL("CodeTree::visitAllOps");

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

void CodeTree::CompileContext::init()
{
  CALL("CodeTree::CompileContext::init");

  nextVarNum=0;
  varMap.reset();
  nextGlobalVarNum=0;
  globalVarMap.reset();
}

void CodeTree::CompileContext::nextLit()
{
  CALL("CodeTree::CompileContext::nextLit");

  nextVarNum=0;
  varMap.reset();
}

void CodeTree::CompileContext::deinit(CodeTree* tree, bool discarded)
{
  CALL("CodeTree::CompileContext::deinit");

  if(discarded) {
    return;
  }
  //update the max. number of variables, if necessary
  if(nextGlobalVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextGlobalVarNum;
  }
  if(nextVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextVarNum;
  }
}


void CodeTree::compileTerm(Term* trm, CodeStack& code, CompileContext& cctx, bool addLitEnd)
{
  CALL("CodeTree::compileTerm");

  static Stack<unsigned> globalCounterparts;
  globalCounterparts.reset();

  cctx.nextLit();

  if(trm->isLiteral()) {
    Literal* lit=static_cast<Literal*>(trm);
    code.push(OpCode::getTermOp(CHECK_FUN, lit->header()));
  }
  else {
    code.push(OpCode::getTermOp(CHECK_FUN, trm->functor()));
  }
  
  SubtermIterator sti(trm);
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
    ASS(trm->isLiteral());  //LIT_END operation makes sense only for literals
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
CodeTree::CodeBlock* CodeTree::buildBlock(CodeStack& code, size_t cnt, ILStruct* prev)
{
  CALL("CodeTree::buildBlock");

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
void CodeTree::incorporate(CodeStack& code)
{
  CALL("CodeTree::incorporate");
  ASS(code.top().isSuccess());

  if(isEmpty()) {
    _entryPoint=buildBlock(code, code.length(), 0);
    code.reset();
    return;
  }
  
  static const unsigned checkFunOpThreshold=5; //must be greater than 1 or it would cause loops

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

void CodeTree::compressCheckFnOps(OpCode* chainStart)
{
  CALL("CodeTree::compressCheckFnOps");
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

//////////// removal //////////////

void CodeTree::optimizeMemoryAfterRemoval(Stack<OpCode*>* firstsInBlocks, OpCode* removedOp)
{
  CALL("CodeTree::optimizeMemoryAfterRemoval");
  ASS(removedOp->isFail());
  LOG_OP("Code tree removal memory optimization");
  LOG_OP("firstsInBlocks->size()="<<firstsInBlocks->size());
  
  //now let us remove unnecessary instructions and the free memory

  OpCode* op=removedOp;
  ASS(firstsInBlocks->isNonEmpty());
  OpCode* firstOp=firstsInBlocks->pop();
  for(;;) {
    //firstOp is in a CodeBlock
    ASS(!firstOp->isSearchStruct());
    //op is in the CodeBlock starting at firstOp
    ASS_LE(firstOp, op);
    ASS_G(firstOp+firstOpToCodeBlock(firstOp)->length(), op);

    int firstOpFun= firstOp->isCheckFun() ? firstOp->arg() : -1;
    
    while(op>firstOp && !op->alternative) { ASS(!op->isSuccess()); op--; }
    
    ASS(!op->isSuccess());

    if(op!=firstOp) {
      ASS(op->alternative);
      //we only change the instruction, the alternative must remain unchanged
      op->makeFail();
      return;
    }
    OpCode* alt=firstOp->alternative;

    CodeBlock* cb=firstOpToCodeBlock(firstOp);

    if(firstsInBlocks->isEmpty() && alt && alt->isSearchStruct()) {
      //We should remove the CodeBlock referenced by _entryPoint, but
      //we cannot replace it by its alternative as it is not a CodeBlock
      //(it's a SearchStruct). Therefore w will not delete it, just set 
      //the first operation to fail.
      ASS_EQ(cb,_entryPoint);
      firstOp->makeFail();
      return;
    }
    
    if(_clauseCodeTree) {
      //delete ILStruct objects
      size_t cbLen=cb->length();
      for(size_t i=0;i<cbLen;i++) {
	if((*cb)[i].isLitEnd()) {
	  delete (*cb)[i].getILS();
	}
      }
    }
    cb->deallocate(); //from now on we mustn't dereference firstOp
    
    if(firstsInBlocks->isEmpty()) {
      ASS(!alt || !alt->isSearchStruct());
      ASS_EQ(cb,_entryPoint);
      _entryPoint=alt ? firstOpToCodeBlock(alt) : 0;
      return;
    }

    //first operation in the CodeBlock that points to the current one (i.e. cb)
    OpCode* prevFirstOp=firstsInBlocks->pop();
    
    if(prevFirstOp->isSearchStruct()) {
      SearchStruct* ss=prevFirstOp->getSearchStruct();
      if(prevFirstOp->alternative==firstOp) {
	//firstOp was an alternative to the SearchStruct
	prevFirstOp->alternative=alt;
	return;
      }
      ASS_GE(firstOpFun,0);
      ASS_EQ(ss->targetOp(firstOpFun), firstOp);

      ss->targetOp(firstOpFun)=alt;
      if(alt) {
	ASS(alt->isCheckFun());
	return;
      }
      for(size_t i=0; i<ss->length; i++) {
	if(ss->targets[i]!=0) {
	  //the SearchStruct still contains something, so we won't delete it
	  //TODO: we might want to compress the SearchStruct, if there are too many zeroes
	  return;
	}
      }
      firstOp=&ss->landingOp;
      alt=ss->landingOp.alternative;
      delete ss;
      
      //now let's continue as if there wasn't any SEARCH_STRUCT operation:)
      
      //the SEARCH_STRUCT is never the first operation in the CodeTree
      ASS(firstsInBlocks->isNonEmpty());
      prevFirstOp=firstsInBlocks->pop();
      //there never are two nested SEARCH_STRUCT operations
      ASS(!prevFirstOp->isSearchStruct());
    }

    CodeBlock* pcb=firstOpToCodeBlock(prevFirstOp);

    //operation that points to the current CodeBlock
    OpCode* pointingOp=0;

    OpCode* prevAfterLastOp=prevFirstOp+pcb->length();
    OpCode* prevOp=prevFirstOp;
    while(prevOp->alternative!=firstOp) {
      ASS_L(prevOp,prevAfterLastOp);
      prevOp++;
    }
    pointingOp=prevOp;

    pointingOp->alternative=alt;
    if(pointingOp->isSuccess()) {
      return;
    }
    
    prevOp++;
    while(prevOp!=prevAfterLastOp) {
      ASS_NEQ(prevOp->alternative,firstOp);

      if(prevOp->alternative || prevOp->isSuccess()) {
	//there is an operation after the pointingOp that cannot be lost
	return;
      }
      prevOp++;
    }
    
    firstOp=prevFirstOp;
    op=pointingOp;
  }
}

void CodeTree::RemovingMatcher::init(OpCode* entry_, LitInfo* linfos_,
    size_t linfoCnt_, CodeTree* tree_, Stack<OpCode*>* firstsInBlocks_)
{
  CALL("CodeTree::RemovingMatcher::init");
  
  fresh=true;
  entry=entry_;
  linfos=linfos_;
  linfoCnt=linfoCnt_;
  tree=tree_;
  firstsInBlocks=firstsInBlocks_;
  
  initFIBDepth=firstsInBlocks->size();

  matchingClauses=tree->_clauseCodeTree;
  bindings.ensure(tree->_maxVarCnt);
  btStack.reset();
  
  curLInfo=0;
}

bool CodeTree::RemovingMatcher::next()
{
  CALL("CodeTree::RemovingMatcher::next");

  if(fresh) {
    fresh=false;
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
      btStack.push(BTPoint(tp, op->alternative, firstsInBlocks->size()));
    }
    LOG_OP(tp<<':'<<op->instr());
    switch(op->instr()) {
    case CHECK_FUN:
      shouldBacktrack=!doCheckFun();
      break;
    case ASSIGN_VAR:
      shouldBacktrack=!doAssignVar();
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
      ASS(matchingClauses);
      return true;
    case SUCCESS_OR_FAIL:
      if(op->isFail()) {
	shouldBacktrack=true;
	break;
      }
    case SUCCESS2:
      if(matchingClauses) {
	//we can succeed only in certain depth and that will be handled separately
	shouldBacktrack=true;
      }
      else {
	//we are matching terms in a TermCodeTree
	return true;
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

bool CodeTree::RemovingMatcher::backtrack()
{
  CALL("CodeTree::RemovingMatcher::backtrack");
  
  if(btStack.isEmpty()) {
    curLInfo++;
    return prepareLiteral();
  }
  BTPoint bp=btStack.pop();
  tp=bp.tp;
  op=bp.op;
  firstsInBlocks->truncate(bp.fibDepth);
  firstsInBlocks->push(op);
  return true;
}

bool CodeTree::RemovingMatcher::prepareLiteral()
{
  CALL("CodeTree::RemovingMatcher::prepareLiteral");

  firstsInBlocks->truncate(initFIBDepth);
  if(curLInfo>=linfoCnt) {
    return false;
  }
  ft=linfos[curLInfo].ft;
  tp=0;
  op=entry;
  return true;
}

inline bool CodeTree::RemovingMatcher::doSearchStruct()
{
  CALL("CodeTree::RemovingMatcher::doSearchStruct");
  ASS_EQ(op->instr(), SEARCH_STRUCT);
  
  const FlatTerm::Entry& fte=(*ft)[tp];
  if(!fte.isFun()) {
    return false;
  }
  OpCode* target=op->getSearchStruct()->targetOp(fte.number());
  if(!target) {
    return false;
  }
  op=target;
  firstsInBlocks->push(op);
  return true;
}

inline bool CodeTree::RemovingMatcher::doCheckFun()
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

inline bool CodeTree::RemovingMatcher::doAssignVar()
{
  ASS_EQ(op->instr(), ASSIGN_VAR);

  //we are looking for variants and they match only other variables into variables
  unsigned var=op->arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(fte->tag()!=FlatTerm::VAR) {
    return false;
  }
  bindings[var]=fte->number();
  tp++;
  return true;
}

inline bool CodeTree::RemovingMatcher::doCheckVar()
{
  ASS_EQ(op->instr(), CHECK_VAR);

  //we are looking for variants and they match only other variables into variables
  unsigned var=op->arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(fte->tag()!=FlatTerm::VAR || bindings[var]!=fte->number()) {
    return false;
  }
  tp++;
  return true;
}



//////////////// retrieval ////////////////////

void CodeTree::incTimeStamp()
{
  _curTimeStamp++;
  if(!_curTimeStamp) {
    //handle overflow
    NOT_IMPLEMENTED;
  }
}

void CodeTree::Matcher::init(CodeTree* tree_, OpCode* entry_)
{
  CALL("CodeTree::Matcher::init");

  tree=tree_;
  entry=entry_;

  _fresh=true;
  _matched=false;
  curLInfo=0;
  btStack.reset();
  bindings.ensure(tree->_maxVarCnt);
}

bool CodeTree::Matcher::execute()
{
  CALL("CodeTree::Matcher::execute");

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

bool CodeTree::Matcher::backtrack()
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

bool CodeTree::Matcher::prepareLiteral()
{
  CALL("CodeTree::Matcher::prepareLiteral");

  if(curLInfo>=linfoCnt) {
    return false;
  }
  tp=0;
  op=entry;
  ft=linfos[curLInfo].ft;
  return true;
}

inline bool CodeTree::Matcher::doSearchStruct()
{
  ASS_EQ(op->instr(), SEARCH_STRUCT);

  const FlatTerm::Entry& fte=(*ft)[tp];
  if(!fte.isFun()) {
    return false;
  }
  op=op->getSearchStruct()->targetOp(fte.number());
  return op;
}

inline bool CodeTree::Matcher::doCheckFun()
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

inline void CodeTree::Matcher::doAssignVar()
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

inline bool CodeTree::Matcher::doCheckVar()
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



}









































