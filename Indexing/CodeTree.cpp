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
 * @file CodeTree.cpp
 * Implements class CodeTree.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/BitUtils.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Portability.hpp"
#include "Lib/Sort.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "CodeTree.hpp"

#define GROUND_TERM_CHECK 0

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

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
#if GROUND_TERM_CHECK
  ASS_EQ((*ft)[1].tag(), FlatTerm::FUN_TERM_PTR);
  (*ft)[1]._ptr=Literal::oppositeLiteral(static_cast<Literal*>((*ft)[1].ptr()));
#endif

  LitInfo res=li;
  res.ft=ft;
  res.opposite=true;
#if VDEBUG
  res.liIndex=-1; //the liIndex has to be updated by caller
#endif
  return res;
}


/**
 * Allocate a MatchInfo object having @b bindCnt binding positions.
 */
CodeTree::MatchInfo* CodeTree::MatchInfo::alloc(unsigned bindCnt)
{
  CALL("MatchInfo::alloc");

  //We have to get sizeof(MatchInfo) + (bindCnt-1)*sizeof(TermList)
  //this way, because bindCnt-1 wouldn't behave well for
  //bindCnt==0 on x64 platform.
  size_t size=sizeof(MatchInfo)+bindCnt*sizeof(TermList);
  size-=sizeof(TermList);

  void* mem=ALLOC_KNOWN(size,"CodeTree::MatchInfo");
  return reinterpret_cast<MatchInfo*>(mem);
}

/**
 * Destroy the MatchInfo object with @b bindCnt bindings
 */
void CodeTree::MatchInfo::destroy(unsigned bindCnt)
{
  CALL("MatchInfo::destroy");

  //We have to get sizeof(MatchInfo) + (bindCnt-1)*sizeof(TermList)
  //this way, because bindCnt-1 wouldn't behave well for
  //bindCnt==0 on x64 platform.
  size_t size=sizeof(MatchInfo)+bindCnt*sizeof(TermList);
  size-=sizeof(TermList);

  DEALLOC_KNOWN(this, size,"CodeTree::MatchInfo");
}


void CodeTree::MatchInfo::init(ILStruct* ils, unsigned liIndex_, DArray<TermList>& bindingArray)
{
  liIndex=liIndex_;
  size_t bindCnt=ils->varCnt;
  if(bindCnt) {
    unsigned* perm=ils->globalVarPermutation;
    for(size_t i=0;i<bindCnt;i++) {
      bindings[perm[i]]=bindingArray[i];
    }
  }
}


CodeTree::ILStruct::ILStruct(Literal* lit, unsigned varCnt, Stack<unsigned>& gvnStack)
: varCnt(varCnt), sortedGlobalVarNumbers(0), globalVarPermutation(0), timestamp(0)
{
  ASS_EQ(matches.size(), 0); //we don't want any uninitialized pointers in the array

  if(varCnt) {
    size_t gvnSize=sizeof(unsigned)*varCnt;
    globalVarNumbers=static_cast<unsigned*>(
	ALLOC_KNOWN(gvnSize, "CodeTree::ILStruct::globalVarNumbers"));
    memcpy(globalVarNumbers, gvnStack.begin(), gvnSize);
  }
  else {
    globalVarNumbers=0;
  }
  if(lit->isTwoVarEquality()) {
    isVarEqLit = 1;
    varEqLitSort = lit->twoVarEqSort();
  }
  else {
    isVarEqLit = 0;
  }
}

CodeTree::ILStruct::~ILStruct()
{
  size_t msize=matches.size();
  for(size_t i=0;i<msize;i++) {
    if(matches[i]) {
      matches[i]->destroy(varCnt);
    }
    else {
      //non-zero entries are only in the beginning of the matches array
      break;
    }
  }

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

  //LIT_END is always at the end of the term and we ask for op matching only
  //if the prefixes were equal. In this case the number of variables and the fact
  //the literal is an equality between variables should be the same on both literals.
  ASS_EQ(varCnt,o.varCnt);
  ASS_EQ(isVarEqLit,o.isVarEqLit);

  if(isVarEqLit!=o.isVarEqLit || (isVarEqLit && varEqLitSort!=o.varEqLitSort)) {
    return false;
  }
  if(varCnt!=o.varCnt) {
    return false;
  }
  size_t gvnSize=sizeof(unsigned)*varCnt;
  return BitUtils::memEqual(globalVarNumbers, o.globalVarNumbers, gvnSize);
}

void CodeTree::ILStruct::ensureFreshness(unsigned globalTimestamp)
{
  CALL("CodeTree::ILStruct::ensureFreshness");

  if(timestamp!=globalTimestamp) {
    timestamp=globalTimestamp;
    visited=false;
    finished=false;
    noNonOppositeMatches=false;
    matchCnt=0;
  }
}

void CodeTree::ILStruct::addMatch(unsigned liIndex, DArray<TermList>& bindingArray)
{
  CALL("CodeTree::ILStruct::addMatch");

  if(matchCnt==matches.size()) {
    matches.expand(matchCnt ? (matchCnt*2) : 4);
    size_t newSize=matches.size();
    for(size_t i=matchCnt;i<newSize;i++) {
      matches[i]=0;
    }
  }
  ASS_L(matchCnt,matches.size());
  if(!matches[matchCnt]) {
    matches[matchCnt]=MatchInfo::alloc(varCnt);
  }
  matches[matchCnt]->init(this, liIndex, bindingArray);
  matchCnt++;
}

/**
 * Remove match from the set of matches. It puts the last match in
 * the place of the current match. Therefore one should not rely on the
 * order of matches (at least those of index greater than matchIndex)
 * between calls to this function. When one traverses all the matches
 * to filter them by this function, the traversal should go from higher
 * indexes down to zero.
 */
void CodeTree::ILStruct::deleteMatch(unsigned matchIndex)
{
  CALL("CodeTree::ILStruct::deleteMatch");
  ASS_L(matchIndex, matchCnt);

  matchCnt--;
  swap(matches[matchIndex], matches[matchCnt]);
}

CodeTree::MatchInfo*& CodeTree::ILStruct::getMatch(unsigned matchIndex)
{
  CALL("CodeTree::ILStruct::getMatch");
  ASS(!finished);
  ASS_L(matchIndex, matchCnt);
  ASS(matches[matchIndex]);

  return matches[matchIndex];
}

CodeTree::CodeOp CodeTree::CodeOp::getSuccess(void* ptr)
{
  CALL("CodeTree::CodeOp::getSuccess");
  ASS(ptr); //data has to be a non-zero pointer

  CodeOp res;
  res.setAlternative(0);
  res._result=ptr;
  ASS(res.isSuccess());
  return res;
}
CodeTree::CodeOp CodeTree::CodeOp::getLitEnd(ILStruct* ils)
{
  CALL("CodeTree::CodeOp::getLitEnd");

  CodeOp res;
  res.setAlternative(0);
  res._data=reinterpret_cast<size_t>(ils)|LIT_END;
  ASS(res.isLitEnd());
  return res;
}
CodeTree::CodeOp CodeTree::CodeOp::getTermOp(InstructionSuffix i, unsigned num)
{
  CALL("CodeTree::CodeOp::getTermOp");
  ASS(i==CHECK_FUN || i==CHECK_VAR || i==ASSIGN_VAR);

  CodeOp res;
  res.setAlternative(0);
  res.setLongInstr(i);
  res.setArg(num);
  return res;
}

CodeTree::CodeOp CodeTree::CodeOp::getGroundTermCheck(Term* trm)
{
  CALL("CodeTree::CodeOp::getGroundTermCheck");
  ASS(trm->ground());

  CodeOp res;
  res.setAlternative(0);
  res._data=reinterpret_cast<size_t>(trm)|CHECK_GROUND_TERM;
  ASS(res.isCheckGroundTerm());
  return res;
}

/**
 * Return true iff @b o is equal to the object for the purpose
 * of operation matching during cide insertion into the tree
 */
bool CodeTree::CodeOp::equalsForOpMatching(const CodeOp& o) const
{
  CALL("CodeTree::CodeOp::equalsForOpMatching");

  if(instrPrefix()!=o.instrPrefix()) {
    return false;
  }
  switch(instrPrefix()) {
  case LIT_END:
    return getILS()->equalsForOpMatching(*o.getILS());
  case SUCCESS_OR_FAIL:
  case CHECK_GROUND_TERM:
    return data()==o.data();
  case SUFFIX_INSTR:
    //SEARCH_STRUCT operations in the tree should be handled separately
    //during insertion into the code tree
    ASS_NEQ(instrSuffix(), SEARCH_STRUCT);
    return instrSuffix()==o.instrSuffix() && arg()==o.arg();
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
}

CodeTree::SearchStruct* CodeTree::CodeOp::getSearchStruct()
{
  CALL("CodeTree::CodeOp::getSearchStruct");

  //the following line gives warning for not being according
  //to the standard, so we have to work around
//  static const size_t opOfs=offsetof(SearchStruct,landingOp);
  static const size_t opOfs=reinterpret_cast<size_t>(
	&reinterpret_cast<SearchStruct*>(8)->landingOp)-8;

  SearchStruct* res=reinterpret_cast<SearchStruct*>(
      reinterpret_cast<size_t>(this)-opOfs);

  return res;
}

CodeTree::SearchStruct::SearchStruct(Kind kind)
: kind(kind)
{
  CALL("CodeTree::SearchStruct::SearchStruct");

  landingOp.setAlternative(0);
  landingOp.setLongInstr(SEARCH_STRUCT);
}

void CodeTree::SearchStruct::destroy()
{
  CALL("CodeTree::SearchStruct::destroy");

  switch(kind) {
  case FN_STRUCT:
    delete static_cast<FnSearchStruct*>(this);
    break;
  case GROUND_TERM_STRUCT:
    delete static_cast<GroundTermSearchStruct*>(this);
    break;
  }
}

bool CodeTree::SearchStruct::getTargetOpPtr(const CodeOp& insertedOp, CodeOp**& tgt)
{
  CALL("CodeTree::SearchStruct::getTargetOpPtr(const CodeOp&...)");

  switch(kind) {
  case FN_STRUCT:
    if(!insertedOp.isCheckFun()) { return false; }
    tgt=&static_cast<FnSearchStruct*>(this)->targetOp(insertedOp.arg());
    return true;
  case GROUND_TERM_STRUCT:
    if(!insertedOp.isCheckGroundTerm()) { return false; }
    tgt=&static_cast<GroundTermSearchStruct*>(this)->targetOp(insertedOp.getTargetTerm());
    return true;
  default:
    ASSERTION_VIOLATION;
  }
}

CodeTree::CodeOp* CodeTree::SearchStruct::getTargetOp(const FlatTerm::Entry* ftPos)
{
  CALL("CodeTree::SearchStruct::getTargetOp");

  if(!ftPos->isFun()) { return 0; }
  switch(kind) {
  case FN_STRUCT:
    return static_cast<FnSearchStruct*>(this)->targetOp(ftPos->number());
  case GROUND_TERM_STRUCT:
    ftPos++;
    ASS_EQ(ftPos->tag(), FlatTerm::FUN_TERM_PTR);
    return static_cast<GroundTermSearchStruct*>(this)->targetOp(ftPos->ptr());
  default:
    ASSERTION_VIOLATION;
  }
}

CodeTree::FixedSearchStruct::FixedSearchStruct(Kind kind, size_t length)
: SearchStruct(kind), length(length)
{
  CALL("CodeTree::FixedSearchStruct::FixedSearchStruct");
  ASS(length);

  size_t tgtSize=sizeof(CodeOp*)*length;
  targets=static_cast<CodeOp**>(
      ALLOC_KNOWN(tgtSize, "CodeTree::FixedSearchStruct::targets"));
}

CodeTree::FixedSearchStruct::~FixedSearchStruct()
{
  CALL("CodeTree::FixedSearchStruct::~FixedSearchStruct");

  size_t tgtSize=sizeof(CodeOp*)*length;
    DEALLOC_KNOWN(targets, tgtSize, "CodeTree::FixedSearchStruct::targets");
}

CodeTree::GroundTermSearchStruct::GroundTermSearchStruct(size_t length)
: FixedSearchStruct(GROUND_TERM_STRUCT, length)
{
  CALL("CodeTree::GroundTermSearchStruct::GroundTermSearchStruct");
  ASS(length);

  size_t valSize=sizeof(Term*)*length;
  values=static_cast<Term**>(
      ALLOC_KNOWN(valSize, "CodeTree::GroundTermSearchStruct::values"));
}

CodeTree::GroundTermSearchStruct::~GroundTermSearchStruct()
{
  CALL("CodeTree::GroundTermSearchStruct::~GroundTermSearchStruct");

  size_t valSize=sizeof(Term*)*length;
  DEALLOC_KNOWN(values, valSize, "CodeTree::GroundTermSearchStruct::values");
}

CodeTree::CodeOp*& CodeTree::GroundTermSearchStruct::targetOp(const Term* trm)
{
  CALL("CodeTree::GroundTermSearchStruct::findTargetOp");

  size_t left=0;
  size_t right=length-1;
  while(left<right) {
    size_t mid=(left+right)/2;
    switch(Int::compare(trm, values[mid])) {
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
  ASS(left==length-1 || trm<=values[left]);
  return targets[left];
}

/**
 * Comparator that compares two CHECK_GROUND_TERM operations for the
 * purpose of insertion into the FnSearchStruct.
 *
 * Is used in the @b compressCheckGroundTermOps function.
 */
struct CodeTree::GroundTermSearchStruct::OpComparator
{
  static Comparison compare(CodeOp* op1, CodeOp* op2)
  {
    return Int::compare(op1->getTargetTerm(), op2->getTargetTerm());
  }
};

CodeTree::FnSearchStruct::FnSearchStruct(size_t length)
: FixedSearchStruct(FN_STRUCT, length)
{
  CALL("CodeTree::FnSearchStruct::FnSearchStruct");
  ASS(length);

  size_t valSize=sizeof(unsigned)*length;
  values=static_cast<unsigned*>(
      ALLOC_KNOWN(valSize, "CodeTree::SearchStruct::values"));
}

CodeTree::FnSearchStruct::~FnSearchStruct()
{
  CALL("CodeTree::FnSearchStruct::~FnSearchStruct");

  size_t valSize=sizeof(unsigned)*length;
  DEALLOC_KNOWN(values, valSize, "CodeTree::SearchStruct::values");
}

CodeTree::CodeOp*& CodeTree::FnSearchStruct::targetOp(unsigned fn)
{
  CALL("CodeTree::FnSearchStruct::findTargetOp");

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
 * purpose of insertion into the FnSearchStruct.
 *
 * Is used in the @b compressCheckFnOps function.
 */
struct CodeTree::FnSearchStruct::OpComparator
{
  static Comparison compare(CodeOp* op1, CodeOp* op2)
  {
    return Int::compare(op1->arg(), op2->arg());
  }
};


inline bool CodeTree::BaseMatcher::doCheckGroundTerm()
{
  ASS_EQ(op->instrPrefix(), CHECK_GROUND_TERM);

  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(!fte->isFun()) {
    return false;
  }

  Term* trm=op->getTargetTerm();

  fte++;
  ASS_EQ(fte->tag(), FlatTerm::FUN_TERM_PTR);
  ASS(fte->ptr());
  if(trm!=fte->ptr()) {
    return false;
  }
  fte++;
  ASS_EQ(fte->tag(), FlatTerm::FUN_RIGHT_OFS);
  tp+=fte->number();
  return true;
}

//////////////// auxiliary ////////////////////

CodeTree::CodeTree()
: _onCodeOpDestroying(0), _curTimeStamp(0), _maxVarCnt(1), _entryPoint(0)
{
}

CodeTree::~CodeTree()
{
  CALL("CodeTree::~CodeTree");
      
  static Stack<CodeOp*> top_ops; 
  // each top_op is either a first op of a Block or a SearchStruct
  // but it cannot be both since SearchStructs don't occur inside blocks
  top_ops.reset();

  if(!isEmpty()) { top_ops.push(getEntryPoint()); }

  while(top_ops.isNonEmpty()) {
    CodeOp* top_op = top_ops.pop();
            
    if (top_op->isSearchStruct()) {            
      if(top_op->alternative()) {
        top_ops.push(top_op->alternative());
      }
      
      FixedSearchStruct* ss = static_cast<FixedSearchStruct*> (top_op->getSearchStruct());
      ASS(ss->isFixedSearchStruct());      
      for (size_t i = 0; i < ss->length; i++) {
        if (ss->targets[i]!=0) { // zeros are allowed as targets (they are holes after removals)
          top_ops.push(ss->targets[i]);
        }
      }
      ss->destroy();
    } else {
      CodeBlock* cb=firstOpToCodeBlock(top_op);

      CodeOp* op=&(*cb)[0];
      ASS_EQ(top_op,op);
      for(size_t rem=cb->length(); rem; rem--,op++) {
        if (_onCodeOpDestroying) {
          (*_onCodeOpDestroying)(op); 
        }
        if(op->alternative()) {
          top_ops.push(op->alternative());
        }
      }
      cb->deallocate();
    }
  }
}

/**
 * Return CodeBlock which contains @b op as its first operation
 */
CodeTree::CodeBlock* CodeTree::firstOpToCodeBlock(CodeOp* op)
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

  static Stack<CodeOp*> top_ops; 
  // each top_op is either a first op of a Block or a SearchStruct
  // but it cannot be both since SearchStructs don't occur inside blocks
  top_ops.reset();

  if(!isEmpty()) { top_ops.push(getEntryPoint()); }

  while(top_ops.isNonEmpty()) {
    CodeOp* top_op = top_ops.pop();
            
    if (top_op->isSearchStruct()) {
      visitor(top_op); // visit the landingOp inside the SearchStruct
      
      if(top_op->alternative()) {
        top_ops.push(top_op->alternative());
      }
      
      FixedSearchStruct* ss = static_cast<FixedSearchStruct*> (top_op->getSearchStruct());
      ASS(ss->isFixedSearchStruct());      
      for (size_t i = 0; i < ss->length; i++) {
        if (ss->targets[i]!=0) { // zeros are allowed as targets (they are holes after removals)
          top_ops.push(ss->targets[i]);
        }
      }              
    } else {
      CodeBlock* cb=firstOpToCodeBlock(top_op);

      CodeOp* op=&(*cb)[0];
      ASS_EQ(top_op,op);
      for(size_t rem=cb->length(); rem; rem--,op++) {
        visitor(op);        
        if(op->alternative()) {
          top_ops.push(op->alternative());
        }
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

  if(GROUND_TERM_CHECK && trm->ground()) {
    code.push(CodeOp::getGroundTermCheck(trm));
  }
  else {
    if(trm->isLiteral()) {
      Literal* lit=static_cast<Literal*>(trm);
      code.push(CodeOp::getTermOp(CHECK_FUN, lit->header()));
    }
    else {
      code.push(CodeOp::getTermOp(CHECK_FUN, trm->functor()));
    }

    SubtermIterator sti(trm);
    while(sti.hasNext()) {
      TermList s=sti.next();
      if(s.isVar()) {
	unsigned var=s.var();
	unsigned* varNumPtr;
	if(cctx.varMap.getValuePtr(var,varNumPtr)) {
	  *varNumPtr=cctx.nextVarNum++;
	  code.push(CodeOp::getTermOp(ASSIGN_VAR, *varNumPtr));

	  if(addLitEnd) {
	    unsigned* globalVarNumPtr;
	    if(cctx.globalVarMap.getValuePtr(var,globalVarNumPtr)) {
	      *globalVarNumPtr=cctx.nextGlobalVarNum++;
	    }
	    globalCounterparts.push(*globalVarNumPtr);
	  }
	}
	else {
	  code.push(CodeOp::getTermOp(CHECK_VAR, *varNumPtr));
	}
      }
      else {
	ASS(s.isTerm());
	Term* t=s.term();

	if(GROUND_TERM_CHECK && t->ground()) {
	  code.push(CodeOp::getGroundTermCheck(t));
	  sti.right();
	}
	else {
	  code.push(CodeOp::getTermOp(CHECK_FUN, t->functor()));
	}
      }
    }
  }

  if(addLitEnd) {
    ASS(trm->isLiteral());  //LIT_END operation makes sense only for literals
    unsigned varCnt=cctx.nextVarNum;
    ASS_EQ(varCnt, globalCounterparts.size());
    ILStruct* ils=new ILStruct(static_cast<Literal*>(trm), varCnt, globalCounterparts);
    code.push(CodeOp::getLitEnd(ils));
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
    CodeOp& op=code[i+sOfs];
    ASS_EQ(op.alternative(),0); //the ops should not have an alternative set yet
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
  static const unsigned checkGroundTermOpThreshold=3; //must be greater than 1 or it would cause loops

  size_t clen=code.length();
  CodeOp** tailTarget;
  size_t matchedCnt;
  ILStruct* lastMatchedILS=0;

  {
    CodeOp* treeOp = getEntryPoint();

    for (size_t i = 0; i < clen; i++) {
      CodeOp* chainStart = treeOp;
      size_t checkFunOps = 0;
      size_t checkGroundTermOps = 0;
      for (;;) {
        if (treeOp->isSearchStruct()) {
          //handle the SEARCH_STRUCT
          SearchStruct* ss = treeOp->getSearchStruct();
          CodeOp** toPtr;
          if (ss->getTargetOpPtr(code[i], toPtr)) {
            if (!*toPtr) {
              tailTarget = toPtr;
              matchedCnt = i;
              goto matching_done;
            }
            treeOp = *toPtr;
            continue;
          }
        } else if (code[i].equalsForOpMatching(*treeOp)) {
          //matched, go to the next compiled instruction
          break;
        }

        if (treeOp->alternative()) {
          //try alternative if there is some
          treeOp = treeOp->alternative();
        } else {
          //matching failed, we'll add the new branch here
          tailTarget = &treeOp->alternative();
          matchedCnt = i;
          goto matching_done;
        }

        if (treeOp->isCheckFun()) {
          checkFunOps++;
          //if there were too many CHECK_FUN alternative operations, put them
          //into a SEARCH_STRUCT
          if (checkFunOps > checkFunOpThreshold) {
            //we put CHECK_FUN ops into the SEARCH_STRUCT op, and
            //restart with the chain
            compressCheckOps(chainStart, SearchStruct::FN_STRUCT);
            treeOp = chainStart;
            checkFunOps = 0;
            checkGroundTermOps = 0;
            continue;
          }
        }

        if (treeOp->isCheckGroundTerm()) {
          checkGroundTermOps++;
          //if there were too many CHECK_GROUND_TERM alternative operations, put them
          //into a SEARCH_STRUCT
          if (checkGroundTermOps > checkGroundTermOpThreshold) {
            //we put CHECK_GROUND_TERM ops into the SEARCH_STRUCT op, and
            //restart with the chain
            compressCheckOps(chainStart, SearchStruct::GROUND_TERM_STRUCT);
            treeOp = chainStart;
            checkFunOps = 0;
            checkGroundTermOps = 0;
            continue;
          }
        }
      } // for(;;) 

      if (treeOp->isLitEnd()) {
        lastMatchedILS = treeOp->getILS();
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
    matchedCnt = clen - 1;

    //we need to find where to put it
    while (treeOp->alternative()) {
      treeOp = treeOp->alternative();
    }
    tailTarget = &treeOp->alternative();
  }
matching_done:

  ASS_L(matchedCnt,clen);
  RSTAT_MCTR_INC("alt split literal", lastMatchedILS ? (lastMatchedILS->depth+1) : 0);

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

void CodeTree::compressCheckOps(CodeOp* chainStart, SearchStruct::Kind kind)
{
  CALL("CodeTree::compressCheckOps");
  ASS(chainStart->alternative());

  static Stack<CodeOp*> toDo;
  static Stack<CodeOp*> chfOps;
  static Stack<CodeOp*> otherOps;
  toDo.reset();
  chfOps.reset();
  otherOps.reset();

  toDo.push(chainStart->alternative());
  while (toDo.isNonEmpty()) {
    CodeOp* op = toDo.pop();
    if (op->alternative()) {
      toDo.push(op->alternative());
    }
    if ((kind == SearchStruct::FN_STRUCT && op->isCheckFun()) ||
            (kind == SearchStruct::GROUND_TERM_STRUCT && op->isCheckGroundTerm())) {
      chfOps.push(op);
    } else if (op->isSearchStruct()) {
      FixedSearchStruct* ss = static_cast<FixedSearchStruct*> (op->getSearchStruct());
      ASS(ss->isFixedSearchStruct());
      if (ss->kind == kind) {
        for (size_t i = 0; i < ss->length; i++) {
          if (ss->targets[i]) {
            toDo.push(ss->targets[i]);
          }
        }
        ss->destroy();
      } else {
        otherOps.push(op);
      }
    } else {
      otherOps.push(op);
    }
  }

  ASS_G(chfOps.size(),1);
  size_t slen=chfOps.size();
  SearchStruct* ss;
  if(kind==SearchStruct::FN_STRUCT) {
    FnSearchStruct* res=new FnSearchStruct(slen);

    sort<FnSearchStruct::OpComparator>(chfOps.begin(), chfOps.end());

    for(size_t i=0;i<slen;i++) {
      ASS(chfOps[i]->isCheckFun());
      res->values[i]=chfOps[i]->arg();
      res->targets[i]=chfOps[i];
      chfOps[i]->setAlternative(0);
    }
    ss=res;
  }
  else {
    ASS_EQ(kind, SearchStruct::GROUND_TERM_STRUCT);
    GroundTermSearchStruct* res=new GroundTermSearchStruct(slen);

    sort<GroundTermSearchStruct::OpComparator>(chfOps.begin(), chfOps.end());

    for(size_t i=0;i<slen;i++) {
      ASS(chfOps[i]->isCheckGroundTerm());
      res->values[i]=chfOps[i]->getTargetTerm();
      res->targets[i]=chfOps[i];
      chfOps[i]->setAlternative(0);
    }
    ss=res;
  }

  CodeOp* op=&ss->landingOp;
  chainStart->setAlternative(op);
  while(otherOps.isNonEmpty()) {
    CodeOp* next=otherOps.pop();
    op->setAlternative(next);
    op=next;
  }
  op->setAlternative(0);
}

//////////// removal //////////////

void CodeTree::optimizeMemoryAfterRemoval(Stack<CodeOp*>* firstsInBlocks, CodeOp* removedOp)
{
  CALL("CodeTree::optimizeMemoryAfterRemoval");
  ASS(removedOp->isFail());
  LOG_OP("Code tree removal memory optimization");
  LOG_OP("firstsInBlocks->size()="<<firstsInBlocks->size());

  //now let us remove unnecessary instructions and the free memory

  CodeOp* op=removedOp;
  ASS(firstsInBlocks->isNonEmpty());
  CodeOp* firstOp=firstsInBlocks->pop();
  for(;;) {
    //firstOp is in a CodeBlock
    ASS(!firstOp->isSearchStruct());
    //op is in the CodeBlock starting at firstOp
    ASS_LE(firstOp, op);
    ASS_G(firstOp+firstOpToCodeBlock(firstOp)->length(), op);

    while(op>firstOp && !op->alternative()) { ASS(!op->isSuccess()); op--; }

    ASS(!op->isSuccess());

    if(op!=firstOp) {
      ASS(op->alternative());
      //we only change the instruction, the alternative must remain unchanged
      op->makeFail();
      return;
    }
    CodeOp* alt=firstOp->alternative();

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

    CodeOp firstOpCopy= *firstOp;

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
    CodeOp* prevFirstOp=firstsInBlocks->pop();

    if(prevFirstOp->isSearchStruct()) {
      if(prevFirstOp->alternative()==firstOp) {
	//firstOp was an alternative to the SearchStruct
	prevFirstOp->setAlternative(alt);
	return;
      }
      FixedSearchStruct* ss=static_cast<FixedSearchStruct*>(prevFirstOp->getSearchStruct());
      ASS(ss->isFixedSearchStruct());
      CodeOp** tgtPtr;
      ALWAYS(ss->getTargetOpPtr(firstOpCopy, tgtPtr));
      ASS_EQ(*tgtPtr, firstOp);
      *tgtPtr=alt;
      if(alt) {
	ASS( (ss->kind==SearchStruct::FN_STRUCT && alt->isCheckFun()) ||
	    (ss->kind==SearchStruct::GROUND_TERM_STRUCT && alt->isCheckGroundTerm()) );
	return;
      }
      for(size_t i=0; i<ss->length; i++) {
	if(ss->targets[i]!=0) {
	  //the SearchStruct still contains something, so we won't delete it
	  //TODO: we might want to compress the SearchStruct, if there are too many zeroes
	  return;
	}
      }

      //if we're at this point, the SEARCH_STRUCT will be deleted
      firstOp=&ss->landingOp;
      alt=ss->landingOp.alternative();
      ss->destroy();

      //now let's continue as if there wasn't any SEARCH_STRUCT operation:)

      //the SEARCH_STRUCT is never the first operation in the CodeTree
      ASS(firstsInBlocks->isNonEmpty());
      prevFirstOp=firstsInBlocks->pop();
      //there never are two nested SEARCH_STRUCT operations
      ASS(!prevFirstOp->isSearchStruct());
    }

    CodeBlock* pcb=firstOpToCodeBlock(prevFirstOp);

    //operation that points to the current CodeBlock
    CodeOp* pointingOp=0;

    CodeOp* prevAfterLastOp=prevFirstOp+pcb->length();
    CodeOp* prevOp=prevFirstOp;
    while(prevOp->alternative()!=firstOp) {
      ASS_L(prevOp,prevAfterLastOp);
      prevOp++;
    }
    pointingOp=prevOp;

    pointingOp->setAlternative(alt);
    if(pointingOp->isSuccess()) {
      return;
    }

    prevOp++;
    while(prevOp!=prevAfterLastOp) {
      ASS_NEQ(prevOp->alternative(),firstOp);

      if(prevOp->alternative() || prevOp->isSuccess()) {
	//there is an operation after the pointingOp that cannot be lost
	return;
      }
      prevOp++;
    }

    firstOp=prevFirstOp;
    op=pointingOp;
  }
}

void CodeTree::RemovingMatcher::init(CodeOp* entry_, LitInfo* linfos_,
    size_t linfoCnt_, CodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_)
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
    if(op->alternative()) {
      btStack.push(BTPoint(tp, op->alternative(), firstsInBlocks->size()));
    }
    switch(op->instrPrefix()) {
    case SUCCESS_OR_FAIL:
      if(op->isFail()) {
	shouldBacktrack=true;
	break;
      }
      if(matchingClauses) {
	//we can succeed only in certain depth and that will be handled separately
	shouldBacktrack=true;
      }
      else {
	//we are matching terms in a TermCodeTree
	return true;
      }
      break;
    case LIT_END:
      ASS(matchingClauses);
      return true;
    case CHECK_GROUND_TERM:
      shouldBacktrack=!doCheckGroundTerm();
      break;
    case SUFFIX_INSTR:
      switch(op->instrSuffix()) {
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
      }
      break;
    }
    if(shouldBacktrack) {
      if(!backtrack()) {
        return false;
      }
      // dead store, left here in case it should have been a static?
      // shouldBacktrack = false;
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
  ASS_EQ(op->instrSuffix(), SEARCH_STRUCT);

  const FlatTerm::Entry* fte=&(*ft)[tp];
  CodeOp* target=op->getSearchStruct()->getTargetOp(fte);
  if(!target) {
    return false;
  }
  op=target;
  firstsInBlocks->push(op);
  return true;
}

inline bool CodeTree::RemovingMatcher::doCheckFun()
{
  ASS_EQ(op->instrSuffix(), CHECK_FUN);

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
  ASS_EQ(op->instrSuffix(), ASSIGN_VAR);

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
  ASS_EQ(op->instrSuffix(), CHECK_VAR);

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

void CodeTree::Matcher::init(CodeTree* tree_, CodeOp* entry_)
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
    if(op->alternative()) {
      btStack.push(BTPoint(tp, op->alternative()));
    }
    switch(op->instrPrefix()) {
    case SUCCESS_OR_FAIL:
      if(op->isFail()) {
	shouldBacktrack=true;
	break;
      }
      //yield successes only in the first round (we don't want to yield the
      //same thing for each query literal)
      if(curLInfo==0) {
	return true;
      }
      else {
	shouldBacktrack=true;
      }
      break;
    case LIT_END:
      return true;
    case CHECK_GROUND_TERM:
      shouldBacktrack=!doCheckGroundTerm();
      break;
    case SUFFIX_INSTR:
      switch(op->instrSuffix()) {
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
      }
      break;
    }
    if(shouldBacktrack) {
      if(!backtrack()) {
	return false;
      }
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

/**
 * Is called when we need to retrieve a new result.
 * It does not only backtrack to the next alternative to try,
 * but if there are no more alternatives, it goes back to the
 * entry point and starts evaluating new literal info (if there
 * is some left).
 */
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
  ASS_EQ(op->instrSuffix(), SEARCH_STRUCT);

  const FlatTerm::Entry* fte=&(*ft)[tp];
  op=op->getSearchStruct()->getTargetOp(fte);
  return op;
}

inline bool CodeTree::Matcher::doCheckFun()
{
  ASS_EQ(op->instrSuffix(), CHECK_FUN);

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
  ASS_EQ(op->instrSuffix(), ASSIGN_VAR);

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
  ASS_EQ(op->instrSuffix(), CHECK_VAR);

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
