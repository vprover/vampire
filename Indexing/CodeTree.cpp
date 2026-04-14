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
#include <cstdlib>
#include <cstring>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "CodeTree.hpp"
#include "CopyPatchJit.hpp"

#define GROUND_TERM_CHECK 0

#undef RSTAT_COLLECTION
#define RSTAT_COLLECTION 0

static_assert(sizeof(TermList) == 8, "JIT assumes sizeof(TermList) == 8 for bindings indexing");
static_assert(sizeof(FlatTerm::Entry) == 8, "JIT assumes sizeof(FlatTerm::Entry) == 8 for ft indexing");

namespace Indexing
{

#define GET_CONTAINING_OBJECT_CONST(ContainingClass,MemberField,object) \
  reinterpret_cast<const ContainingClass*>(reinterpret_cast<const char*>(object)-offsetof(ContainingClass,MemberField))

#define GET_CONTAINING_OBJECT(ContainingClass,MemberField,object) \
  reinterpret_cast<ContainingClass*>(reinterpret_cast<char*>(object)-offsetof(ContainingClass,MemberField))

using namespace std;
using namespace Lib;
using namespace Kernel;

//////////////// general datastructures ////////////////////

CodeTree::LitInfo::LitInfo(Clause* cl, unsigned litIndex)
: litIndex(litIndex), opposite(false)
{
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
  ASS_EQ((*ft)[1]._tag(), FlatTerm::FUN_TERM_PTR);
  (*ft)[1]._ptr=Literal::complementaryLiteral(static_cast<Literal*>((*ft)[1]._term()));
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


CodeTree::ILStruct::ILStruct(const Literal* lit, unsigned varCnt, Stack<unsigned>& gvnStack)
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
  //LIT_END is always at the end of the term and we ask for op matching only
  //if the prefixes were equal. In this case the number of variables and the fact
  //the literal is an equality between variables should be the same on both literals.
  ASS_EQ(varCnt,o.varCnt);

  if(varCnt!=o.varCnt) {
    return false;
  }
  // avoids passing nullptr to memcmp below,
  // which is technically UB
  if(!varCnt)
    return true;

  ASS(globalVarNumbers)
  ASS(o.globalVarNumbers)
  return std::memcmp(globalVarNumbers, o.globalVarNumbers, varCnt * sizeof(unsigned)) == 0;
}

void CodeTree::ILStruct::ensureFreshness(unsigned globalTimestamp)
{
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
  ASS_L(matchIndex, matchCnt);

  matchCnt--;
  swap(matches[matchIndex], matches[matchCnt]);
}

CodeTree::MatchInfo*& CodeTree::ILStruct::getMatch(unsigned matchIndex)
{
  ASS(!finished);
  ASS_L(matchIndex, matchCnt);
  ASS(matches[matchIndex]);

  return matches[matchIndex];
}

CodeTree::CodeOp CodeTree::CodeOp::getLitEnd(ILStruct* ils)
{
  CodeOp res;
  res._setData(ils);
  res._setInstruction(LIT_END);
  ASS(res.isLitEnd());
  return res;
}

CodeTree::CodeOp CodeTree::CodeOp::getTermOp(Instruction i, unsigned num)
{
  ASS(i==CHECK_FUN || i==CHECK_VAR || i==ASSIGN_VAR);

  CodeOp res;
  res._setInstruction(i);
  res._setArg(num);
  return res;
}

CodeTree::CodeOp CodeTree::CodeOp::getGroundTermCheck(const Term* trm)
{
  ASS(trm->ground());

  CodeOp res;
  res._setData(trm);
  ASS(res.isCheckGroundTerm());
  return res;
}

/**
 * Return true iff @b o is equal to the object for the purpose
 * of operation matching during cide insertion into the tree
 */
bool CodeTree::CodeOp::equalsForOpMatching(const CodeOp& o) const
{
  if(_instruction()!=o._instruction()) {
    return false;
  }
  switch(_instruction()) {
  case LIT_END:
    return getILS()->equalsForOpMatching(*o.getILS());
  case SUCCESS_OR_FAIL:
  case CHECK_GROUND_TERM:
  case CHECK_FUN:
  case ASSIGN_VAR:
  case CHECK_VAR:
    return _content==o._content;
  default:
    //SEARCH_STRUCT operations in the tree should be handled separately
    //during insertion into the code tree
    ASSERTION_VIOLATION;
  }
}

void CodeTree::dumpAllOpsWithAddr(std::ostream& out) const
{
  // out << "==== CodeTree dump @" << (const void*)this << " ====" << std::endl;
  visitAllOps([&out](const CodeTree::CodeOp* op, unsigned depth) {
    for (unsigned i = 0; i < depth; i++) { out << "  "; }
    out << "[op=" << (const void*)op
        << "] mcode=" << (const void*)op->_mcode;
    if (op->alternative()) {
      out << " alt=" << (const void*)op->alternative()
          << " alt_mcode=" << (const void*)op->alternative()->_mcode;
    }
    out << " :: " << *op << std::endl;
    if (op->isSearchStruct()) {
      const auto* ss = op->getSearchStruct();
      for (size_t i = 0; i < ss->targets.size(); i++) {
        const CodeOp* tgt = ss->targets[i];
        for (unsigned j = 0; j < depth+1; j++) { out << "  "; }
        out << "  target[" << i << "]=" << (const void*)tgt;
        if (tgt) { out << " mcode=" << (const void*)tgt->_mcode << " :: " << *tgt; }
        out << std::endl;
      }
    }
  });
  out << "==== end dump ====" << std::endl;
}

const CodeTree::SearchStruct* CodeTree::CodeOp::getSearchStruct() const
{
  ASS(isSearchStruct());
  return GET_CONTAINING_OBJECT_CONST(CodeTree::SearchStruct,landingOp,this);
}

CodeTree::SearchStruct* CodeTree::CodeOp::getSearchStruct()
{
  ASS(isSearchStruct());
  return GET_CONTAINING_OBJECT(CodeTree::SearchStruct,landingOp,this);
}

std::ostream& operator<<(std::ostream& out, const CodeTree::CodeOp& op)
{
  switch (op._instruction()) {
    case CodeTree::SUCCESS_OR_FAIL:
      if (op.isSuccess()) {
        out << "success";
      } else {
        out << "fail";
      }
      break;
    case CodeTree::LIT_END:
      out << "lit end";
      break;
    case CodeTree::CHECK_GROUND_TERM:
      out << "check ground term " << *op.getTargetTerm();
      break;
    case CodeTree::CHECK_FUN:
      out << "check fun " << env.signature->getFunction(op._arg())->name();
      // out << "check fun ";
      break;
    case CodeTree::ASSIGN_VAR:
      out << "assign var X" << op._arg();
      break;
    case CodeTree::CHECK_VAR:
      out << "check var X" << op._arg();
      break;
    case CodeTree::SEARCH_STRUCT:
      out << "search struct ";
      auto ss = op.getSearchStruct();
      switch(ss->kind) {
        case CodeTree::SearchStruct::FN_STRUCT: {
          auto fn_ss = static_cast<const CodeTree::FnSearchStruct*>(ss);
          out << "length " << fn_ss->length();
          for (unsigned i = 0; i < fn_ss->length(); i++) {
            out << " " << fn_ss->values[i] << " ";
            if (fn_ss->targets[i]) {
              out << *fn_ss->targets[i];
            } else {
              out << "nullptr";
            }
          }
          break;
        }
        case CodeTree::SearchStruct::GROUND_TERM_STRUCT: {
          auto gt_ss = static_cast<const CodeTree::GroundTermSearchStruct*>(ss);
          out << "length " << gt_ss->length();
          for (unsigned i = 0; i < gt_ss->length(); i++) {
            out << " " << *gt_ss->values[i] << " ";
            if (gt_ss->targets[i]) {
              out << *gt_ss->targets[i];
            } else {
              out << "nullptr";
            }
          }
          break;
        }
      }
      break;
  }
  return out;
}

CodeTree::SearchStruct::SearchStruct(Kind kind, size_t length)
: kind(kind)
{
  landingOp._setInstruction(SEARCH_STRUCT);
  ASS(length);

  targets.reserve(length);
}

void CodeTree::SearchStruct::destroy()
{
  switch(kind) {
  case FN_STRUCT:
    delete static_cast<FnSearchStruct*>(this);
    break;
  case GROUND_TERM_STRUCT:
    delete static_cast<GroundTermSearchStruct*>(this);
    break;
  }
}

template<bool doInsert>
bool CodeTree::SearchStruct::getTargetOpPtr(const CodeOp& insertedOp, CodeOp**& tgt)
{
  switch(kind) {
  case FN_STRUCT:
    if(!insertedOp.isCheckFun()) { return false; }
    tgt=&static_cast<FnSearchStruct*>(this)->targetOp<doInsert>(insertedOp._arg());
    return true;
  case GROUND_TERM_STRUCT:
    if(!insertedOp.isCheckGroundTerm()) { return false; }
    tgt=&static_cast<GroundTermSearchStruct*>(this)->targetOp<doInsert>(insertedOp.getTargetTerm());
    return true;
  default:
    ASSERTION_VIOLATION;
  }
}

// expose for ClauseCodeTree.cpp
template bool CodeTree::SearchStruct::getTargetOpPtr<false>(const CodeOp&, CodeOp**&);

CodeTree::CodeOp* CodeTree::SearchStruct::getTargetOp(const FlatTerm::Entry* ftPos)
{
  if(!ftPos->isFun()) { return 0; }
  switch(kind) {
  case FN_STRUCT:
    return static_cast<FnSearchStruct*>(this)->targetOp<false>(ftPos->_number());
  case GROUND_TERM_STRUCT:
    ftPos++;
    ASS_EQ(ftPos->_tag(), FlatTerm::FUN_TERM_PTR);
    return static_cast<GroundTermSearchStruct*>(this)->targetOp<false>(ftPos->_term());
  default:
    ASSERTION_VIOLATION;
  }
}

template<CodeTree::SearchStruct::Kind k>
CodeTree::SearchStructImpl<k>::SearchStructImpl(size_t length)
: SearchStruct(k, length)
{
}

template<CodeTree::SearchStruct::Kind k>
template<bool doInsert>
CodeTree::CodeOp*& CodeTree::SearchStructImpl<k>::targetOp(const T& val)
{
  size_t left=0;
  size_t right=length()-1;
  while(left<right) {
    size_t mid=(left+right)/2;
    switch(Int::compare(val, values[mid])) {
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
  ASS(left==length()-1 || val<=values[left]);

  if constexpr (!doInsert) {
    return targets[left];
  }
  if (val==values[left]) {
    return targets[left];
  }

  if (val>=values[left]) {
    left++;
  }
  targets.insert(targets.begin()+left,0);
  values.insert(values.begin()+left,val);
  return targets[left];
}

//////////////// Matcher ////////////////////

template<bool removing, bool checkRange>
bool CodeTree::Matcher<removing, checkRange>::execute()
{
  if(fresh) {
    fresh=false;
  }
  else {
    //we backtrack from what we found in the previous run
    if (!fresh && !backtrack()) {
      _matched = false;
      return false;
    }
    fresh = false;
  }

  bool shouldBacktrack=false;
  for(;;) {
    if(op->alternative()) {
      if constexpr (removing) {
        btStack.push(BTPointRemoving(tp, op->alternative(), RemovingBase::firstsInBlocks->size()));
      } else {
        btStack.push(BTPoint(tp, op->alternative()));
      }
    }
    switch(op->_instruction()) {
      case SUCCESS_OR_FAIL:
        if(op->isFail()) {
          shouldBacktrack=true;
          break;
        }
        if constexpr (removing) {
          if (RemovingBase::matchingClauses) {
            //we can succeed only in certain depth and that will be handled separately
            shouldBacktrack=true;
          }
          else {
            //we are matching terms in a TermCodeTree
            return true;
          }
        } else {
          //yield successes only in the first round (we don't want to yield the
          //same thing for each query literal)
          if(curLInfo==0) {
            return true;
          }
          else {
            shouldBacktrack=true;
          }
        }
        break;
      case LIT_END:
        if constexpr (removing) {
          ASS(RemovingBase::matchingClauses);
        }
        return true;
      case CHECK_GROUND_TERM:
        shouldBacktrack=!doCheckGroundTerm();
        break;
      case CHECK_FUN:
        shouldBacktrack=!doCheckFun();
        break;
      case ASSIGN_VAR:
        if constexpr (removing) {
          shouldBacktrack=!doAssignVar();
        } else {
          doAssignVar();
        }
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

template<bool removing, bool checkRange>
bool CodeTree::Matcher<removing, checkRange>::executeMachineCode()
{
  if constexpr (removing || checkRange) { return execute(); }
  // if (!tree->_clauseCodeTree) { return execute(); }
  if (tree->isEmpty()) { return false; }

  if (!_jitBtBuf) {
    _jitBtBuf = static_cast<BTPoint*>(malloc(JIT_BT_INIT_CAP * sizeof(BTPoint)));
    _jitBtEnd = _jitBtBuf + JIT_BT_INIT_CAP;
    _jitBtCursor = _jitBtBuf;
  }

  if (fresh) {
    fresh = false;
    _jitBtCursor = _jitBtBuf;
  } else {
    // Resume after a previous yield.  Set op = nullptr to signal
    // the trampoline to enter via its backtrack handler, which will
    // pop {tp, mcode} from the JIT bt stack.  If the stack is empty,
    // the trampoline advances to the next literal internally (or
    // returns matched=0 if all literals are exhausted)
    op = nullptr;
  }

  ASS(_jitCtx);
  ASS(_jitFn);
  auto* ctx = static_cast<JitExecContext*>(_jitCtx);
  auto jitFn = reinterpret_cast<CopyPatchJit::TrampolineFunc>(_jitFn);

  ctx->ftData   = &(*ft)[0];
  ctx->tp       = tp;
  ctx->btCursor = _jitBtCursor;
  ctx->btBase   = _jitBtBuf;     // may have changed from expand
  ctx->btEnd    = _jitBtEnd;     // may have changed from expand
  ctx->curLInfo = curLInfo;
  ctx->op       = op;
  ctx->matched  = 0;

  jitFn(ctx);

  // Read back JIT-modified state
  _jitBtBuf    = static_cast<BTPoint*>(ctx->btBase);
  _jitBtCursor = static_cast<BTPoint*>(ctx->btCursor);
  _jitBtEnd    = static_cast<BTPoint*>(ctx->btEnd);
  tp           = ctx->tp;
  op           = static_cast<CodeOp*>(ctx->op);
  curLInfo     = ctx->curLInfo;

  // Keep ft in sync with curLInfo for recordMatch() and other C++ code
  // that accesses linfos[curLInfo] after we return.
  if (linfoCnt > 0 && curLInfo < linfoCnt) {
    ft = linfos[curLInfo].ft;
  }

  if (ctx->matched) { _matched = true; return true; }
  _matched = false;
  return false;
}

template<bool removing, bool checkRange>
void CodeTree::Matcher<removing, checkRange>::init(CodeTree* tree_, CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_, Stack<CodeOp*>* firstsInBlocks_)
{
  tree=tree_;
  entry=entry_;

  linfos=linfos_;
  linfoCnt=linfoCnt_;

  if constexpr (removing) {
    RemovingBase::firstsInBlocks=firstsInBlocks_;
    RemovingBase::initFIBDepth=RemovingBase::firstsInBlocks->size();
    RemovingBase::matchingClauses=tree->_clauseCodeTree;
  }

  fresh=true;
  _matched=false;
  curLInfo=0;

  bindings.ensure(tree->_maxVarCnt);
  btStack.reset();

  // Reset the JIT backtrack cursor (buffer is kept for reuse)
  if constexpr (!removing && !checkRange) {
    _jitBtCursor = _jitBtBuf;

    // constant fields are written once here
    // only per-call fields are updated in executeMachineCode()
    if (tree->_clauseCodeTree && !tree->isEmpty()) {
      if (!_jitCtx) {
        _jitCtx = malloc(sizeof(JitExecContext));
      }
      auto* ctx = static_cast<JitExecContext*>(_jitCtx);
      tree->_cpJit->initContext(*ctx);
      ctx->linfos     = static_cast<void*>(linfos);
      ctx->linfoCnt   = linfoCnt;
      ctx->bindings   = bindings.array();
      ctx->entryMcode = entry ? entry->_mcode : nullptr;
      _jitFn = reinterpret_cast<void*>(tree->_cpJit->trampoline());
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
template<bool removing, bool checkRange>
bool CodeTree::Matcher<removing, checkRange>::backtrack()
{
  if(btStack.isEmpty()) {
    curLInfo++;
    return prepareLiteral();
  }
  auto bp=btStack.pop();
  tp=bp.tp;
  op=bp.op;
  if constexpr (removing) {
    RemovingBase::firstsInBlocks->truncate(bp.fibDepth);
    RemovingBase::firstsInBlocks->push(op);
  }
  return true;
}

template<bool removing, bool checkRange>
bool CodeTree::Matcher<removing, checkRange>::prepareLiteral()
{
  if constexpr (removing) {
    RemovingBase::firstsInBlocks->truncate(RemovingBase::initFIBDepth);
  }
  if(curLInfo>=linfoCnt) {
    return false;
  }
  ft=linfos[curLInfo].ft;
  tp=0;
  op=entry;
  fresh=true;
  return true;
}

template<bool removing, bool checkRange>
inline bool CodeTree::Matcher<removing, checkRange>::doAssignVar()
{
  ASS_EQ(op->_instruction(), ASSIGN_VAR);

  unsigned var=op->_arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(fte->isVar()) {
    if constexpr (checkRange) {
      if (!RemovingBase::range.insert(fte->_number())) {
        return false;
      }
    }
    bindings[var]=TermList::var(fte->_number());
    tp++;
  }
  else {
    // in the removing case we are looking for variants
    // and they match only other variables into variables
    if constexpr (removing) {
      return false;
    }
    ASS(fte->isFun());
    fte++;
    ASS_EQ(fte->_tag(), FlatTerm::FUN_TERM_PTR);
    ASS(fte->_term());
    bindings[var]=TermList(fte->_term());
    fte++;
    ASS_EQ(fte->_tag(), FlatTerm::FUN_RIGHT_OFS);
    tp+=fte->_number();
  }
  return true;
}

template<bool removing, bool checkRange>
inline bool CodeTree::Matcher<removing, checkRange>::doCheckVar()
{
  ASS_EQ(op->_instruction(), CHECK_VAR);

  unsigned var=op->_arg();
  const FlatTerm::Entry* fte=&(*ft)[tp];
  if (fte->isVar()) {
    if(bindings[var]!=TermList::var(fte->_number())) {
      return false;
    }
    tp++;
  }
  else {
    // in the removing case we are looking for variants
    // and they match only other variables into variables
    if constexpr (removing) {
      return false;
    }
    ASS(fte->isFun());
    fte++;
    ASS_EQ(fte->_tag(), FlatTerm::FUN_TERM_PTR);
    if(bindings[var]!=TermList(fte->_term())) {
      return false;
    }
    fte++;
    ASS_EQ(fte->_tag(), FlatTerm::FUN_RIGHT_OFS);
    tp+=fte->_number();
  }
  return true;
}

template<bool removing, bool checkRange>
inline bool CodeTree::Matcher<removing, checkRange>::doCheckFun()
{
  ASS_EQ(op->_instruction(), CHECK_FUN);

  unsigned functor=op->_arg();
  FlatTerm::Entry& fte=(*ft)[tp];
  if(!fte.isFun(functor)) {
    return false;
  }
  fte.expand();
  tp+=FlatTerm::FUNCTION_ENTRY_COUNT;
  return true;
}

template<bool removing, bool checkRange>
inline bool CodeTree::Matcher<removing, checkRange>::doCheckGroundTerm()
{
  ASS_EQ(op->_instruction(), CHECK_GROUND_TERM);

  const FlatTerm::Entry* fte=&(*ft)[tp];
  if(!fte->isFun()) {
    return false;
  }

  Term* trm=op->getTargetTerm();

  fte++;
  ASS_EQ(fte->_tag(), FlatTerm::FUN_TERM_PTR);
  ASS(fte->_term());
  if(trm!=fte->_term()) {
    return false;
  }
  fte++;
  ASS_EQ(fte->_tag(), FlatTerm::FUN_RIGHT_OFS);
  tp+=fte->_number();
  return true;
}

template<bool removing, bool checkRange>
inline bool CodeTree::Matcher<removing, checkRange>::doSearchStruct()
{
  ASS_EQ(op->_instruction(), SEARCH_STRUCT);

  const FlatTerm::Entry* fte=&(*ft)[tp];
  CodeOp* target=op->getSearchStruct()->getTargetOp(fte);
  if(!target) {
    return false;
  }
  op=target;
  if constexpr (removing) {
    RemovingBase::firstsInBlocks->push(op);
  }
  return true;
}

template struct CodeTree::Matcher<true, false>;
template struct CodeTree::Matcher<true, true>;
template struct CodeTree::Matcher<false, false>;

//////////////// auxiliary ////////////////////

CodeTree::CodeTree()
: _curTimeStamp(1), _maxVarCnt(1), _entryPoint(0), _cpJit(new CopyPatchJit())
{
}

CodeTree::~CodeTree()
{
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

      auto ss = top_op->getSearchStruct();
      for (size_t i = 0; i < ss->length(); i++) {
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

  // Release JIT engine and all its executable memory.
  delete _cpJit;
  _cpJit = nullptr;
}

/**
 * Return CodeBlock which contains @b op as its first operation
 */
CodeTree::CodeBlock* CodeTree::firstOpToCodeBlock(CodeOp* op)
{
  ASS(!op->isSearchStruct());
  return GET_CONTAINING_OBJECT(CodeTree::CodeBlock,_array,op);
}


template<class Visitor>
void CodeTree::visitAllOps(Visitor visitor) const
{
  Stack<pair<CodeOp*,unsigned>> top_ops;
  // each top_op is either a first op of a Block or a SearchStruct
  // but it cannot be both since SearchStructs don't occur inside blocks
  top_ops.reset();

  if(!isEmpty()) { top_ops.push(make_pair(getEntryPoint(),0)); }

  while(top_ops.isNonEmpty()) {
    auto kv = top_ops.pop();
    CodeOp* top_op = kv.first;
    unsigned depth = kv.second;

    if (top_op->isSearchStruct()) {
      visitor(top_op, depth); // visit the landingOp inside the SearchStruct

      if(top_op->alternative()) {
        top_ops.push(make_pair(top_op->alternative(),depth));
      }

      auto ss = top_op->getSearchStruct();
      for (size_t i = 0; i < ss->length(); i++) {
        if (ss->targets[i]!=0) { // zeros are allowed as targets (they are holes after removals)
          top_ops.push(make_pair(ss->targets[i],depth+1));
        }
      }
    } else {
      CodeBlock* cb=firstOpToCodeBlock(top_op);

      CodeOp* op=&(*cb)[0];
      ASS_EQ(top_op,op);
      for(size_t rem=cb->length(); rem; rem--,op++) {
        visitor(op, depth+(cb->length()-rem));
        if(op->alternative()) {
          top_ops.push(make_pair(op->alternative(),depth+(cb->length()-rem)));
        }
      }
    }
  }
}

std::ostream& operator<<(std::ostream& out, const CodeTree& ct)
{
  ct.visitAllOps([&out](const CodeTree::CodeOp* op, unsigned depth) {
    for (unsigned i = 0; i < depth; i++) {
      out << "  ";
    }
    out << *op << std::endl;
  });
  return out;
}

//////////////// insertion ////////////////////

template<bool forLits>
CodeTree::Compiler<forLits>::Compiler(CodeStack& code) : code(code), nextVarNum(0), nextGlobalVarNum(0) {}

template<bool forLits>
void CodeTree::Compiler<forLits>::nextLit()
{
  ASS(forLits);
  nextVarNum = 0;
  varMap.reset();
}

template<bool forLits>
void CodeTree::Compiler<forLits>::updateCodeTree(CodeTree* tree)
{
  //update the max. number of variables, if necessary
  if(nextGlobalVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextGlobalVarNum;
  }
  if(nextVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextVarNum;
  }
}

template<bool forLits>
void CodeTree::Compiler<forLits>::handleTerm(const Term* trm)
{
  ASS(!forLits || trm->isLiteral());

  static Stack<unsigned> globalCounterparts;
  globalCounterparts.reset();

  if (GROUND_TERM_CHECK && trm->ground()) {
    code.push(CodeOp::getGroundTermCheck(trm));
    return;
  }

  if (trm->isLiteral()) {
    auto lit = static_cast<const Literal*>(trm);
    code.push(CodeOp::getTermOp(CHECK_FUN, lit->header()));

    // If literal is equality, we add a type argument
    // to properly match with two variable equalities.
    // This has to be done also in flat terms.
    if (lit->isEquality()) {
      auto sort = SortHelper::getEqualityArgumentSort(lit);
      if (sort.isVar()) {
        handleVar(sort.var(), &globalCounterparts);
      } else {
        code.push(CodeOp::getTermOp(CHECK_FUN, sort.term()->functor()));
        handleSubterms(sort.term(), globalCounterparts);
      }
    }
  } else {
    code.push(CodeOp::getTermOp(CHECK_FUN, trm->functor()));
  }

  handleSubterms(trm, globalCounterparts);

  if constexpr (forLits) {
    ASS(trm->isLiteral());  //LIT_END operation makes sense only for literals
    unsigned varCnt = nextVarNum;
    ASS_EQ(varCnt, globalCounterparts.size());
    auto ils = new ILStruct(static_cast<const Literal*>(trm), varCnt, globalCounterparts);
    code.push(CodeOp::getLitEnd(ils));
  }
}

template<bool forLits>
void CodeTree::Compiler<forLits>::handleVar(unsigned var, Stack<unsigned>* globalCounterparts)
{
  unsigned* varNumPtr;
  if (varMap.getValuePtr(var,varNumPtr)) {
    *varNumPtr = nextVarNum++;
    code.push(CodeOp::getTermOp(ASSIGN_VAR, *varNumPtr));

    if constexpr (forLits) {
      unsigned* globalVarNumPtr;
      if (globalVarMap.getValuePtr(var,globalVarNumPtr)) {
        *globalVarNumPtr = nextGlobalVarNum++;
      }
      globalCounterparts->push(*globalVarNumPtr);
    }
  } else {
    code.push(CodeOp::getTermOp(CHECK_VAR, *varNumPtr));
  }
}

template<bool forLits>
void CodeTree::Compiler<forLits>::handleSubterms(const Term* trm, Stack<unsigned>& globalCounterparts)
{
  SubtermIterator sti(trm);
  while (sti.hasNext()) {
    TermList s = sti.next();
    if (s.isVar()) {
      handleVar(s.var(), &globalCounterparts);
      continue;
    }
    ASS(s.isTerm());
    Term* t = s.term();

    if (GROUND_TERM_CHECK && t->ground()) {
      code.push(CodeOp::getGroundTermCheck(t));
      sti.right();
      continue;
    }

    code.push(CodeOp::getTermOp(CHECK_FUN, t->functor()));
  }
}

template struct CodeTree::Compiler<true>;
template struct CodeTree::Compiler<false>;

/**
 * Build CodeBlock object from the last @b cnt instructions on the
 * @b code stack.
 *
 * In this function is also set the value for the @b ILStruct::previous
 * members.
 */
CodeTree::CodeBlock* CodeTree::buildBlock(CodeStack& code, size_t cnt, ILStruct* prev)
{
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
  ASS(code.top().isSuccess());

  if(isEmpty()) {
    _entryPoint=buildBlock(code, code.length(), 0);
    jitBlock(_entryPoint);
    code.reset();
    return;
  }

  static const unsigned checkFunOpThreshold=5; //must be greater than 1 or it would cause loops
  static const unsigned checkGroundTermOpThreshold=3; //must be greater than 1 or it would cause loops

  size_t clen=code.length();
  CodeOp** tailTarget;
  bool tailIsAlternative = false;
  size_t matchedCnt;
  ILStruct* lastMatchedILS=0;
  SearchStruct* modifiedSearchStruct = nullptr;  // Bug 6: track SearchStruct modified by insertion

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
          if (ss->getTargetOpPtr<true>(code[i], toPtr)) {
            if (!*toPtr) {
              tailTarget = toPtr;
              tailIsAlternative = false;
              modifiedSearchStruct = ss;   // track which struct gained a new target slot
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
          tailIsAlternative = true;
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
            compressCheckOps<SearchStruct::FN_STRUCT>(chainStart);
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
            compressCheckOps<SearchStruct::GROUND_TERM_STRUCT>(chainStart);
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
    tailIsAlternative = true;
  }
matching_done:

  ASS_L(matchedCnt,clen);
  RSTAT_MCTR_INC("alt split literal", lastMatchedILS ? (lastMatchedILS->depth+1) : 0);

  CodeBlock* rem=buildBlock(code, clen-matchedCnt, lastMatchedILS);
  CodeOp* newFirst = &(*rem)[0];
  *tailTarget = newFirst;
  // JIT-emit the new block.
  jitBlock(rem);

  if (modifiedSearchStruct) {
    jitSearchStruct(modifiedSearchStruct);
  }
  // Binary-patch the owner's embedded alternative immediate so pushAlt/jmpAlt pick up the new block
  if (tailIsAlternative) {
    CodeOp* owner = reinterpret_cast<CodeOp*>(reinterpret_cast<char*>(tailTarget) - offsetof(CodeOp, _alternative));
    patchAlternative(owner);
  }
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

template<CodeTree::SearchStruct::Kind k>
void CodeTree::compressCheckOps(CodeOp* chainStart)
{
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
    bool ofKind;
    if constexpr (k == SearchStruct::FN_STRUCT) {
      ofKind = op->isCheckFun();
    } else {
      ofKind = op->isCheckGroundTerm();
    }

    if (ofKind) {
      chfOps.push(op);
    } else if (op->isSearchStruct()) {
      auto ss = op->getSearchStruct();
      if (ss->kind == k) {
        for (size_t i = 0; i < ss->length(); i++) {
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
  auto res=new SearchStructImpl<k>(slen);

  sort(chfOps.begin(), chfOps.end(), [](CodeOp* op1, CodeOp* op2) {
    if constexpr (k==SearchStruct::FN_STRUCT) {
      return op1->_arg() < op2->_arg();
    } else {
      return op1->getTargetTerm() < op2->getTargetTerm();
    }
  });

  for(size_t i=0;i<slen;i++) {
    if constexpr (k==SearchStruct::FN_STRUCT) {
      ASS(chfOps[i]->isCheckFun());
      res->values.push_back(chfOps[i]->_arg());
    } else {
      ASS(chfOps[i]->isCheckGroundTerm());
      res->values.push_back(chfOps[i]->getTargetTerm());
    }
    res->targets.push_back(chfOps[i]);
    chfOps[i]->setAlternative(0);
    patchAlternative(chfOps[i]);
  }

  // Install the new SearchStruct into the chain.
  CodeOp* op=&res->landingOp;
  chainStart->setAlternative(op);
  patchAlternative(chainStart);
  while(otherOps.isNonEmpty()) {
    CodeOp* next=otherOps.pop();
    op->setAlternative(next);
    patchAlternative(op);
    op=next;
  }
  op->setAlternative(0);
  patchAlternative(op);

  // JIT-emit machine code for the SearchStruct landing op so that
  // subsequent execution can enter it via op->_mcode.
  jitSearchStruct(res);
}

//////////// removal //////////////

void CodeTree::optimizeMemoryAfterRemoval(Stack<CodeOp*>* firstsInBlocks, CodeOp* removedOp)
{
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
      auto ss = prevFirstOp->getSearchStruct();
      CodeOp** tgtPtr;
      ALWAYS(ss->getTargetOpPtr<false>(firstOpCopy, tgtPtr));
      ASS_EQ(*tgtPtr, firstOp);
      *tgtPtr=alt;
      if(alt) {
	ASS( (ss->kind==SearchStruct::FN_STRUCT && alt->isCheckFun()) ||
	    (ss->kind==SearchStruct::GROUND_TERM_STRUCT && alt->isCheckGroundTerm()) );
	jitSearchStruct(ss);  // Re-emit JIT: target pointer changed
	return;
      }
      for(size_t i=0; i<ss->length(); i++) {
	if(ss->targets[i]!=0) {
	  //the SearchStruct still contains something, so we won't delete it
	  jitSearchStruct(ss);  // Re-emit JIT: target slot nulled out
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
    patchAlternative(pointingOp);
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

//////////////// retrieval ////////////////////

void CodeTree::incTimeStamp()
{
  _curTimeStamp++;
  if(!_curTimeStamp) {
    //handle overflow
    NOT_IMPLEMENTED;
  }
}


//////////////// JIT-delegating to CopyPatchJit ////////////////////

void CodeTree::jitBlock(CodeBlock* block)
{
  _cpJit->initialize();
  _cpJit->emitBlock(block);
}

void CodeTree::jitSearchStruct(SearchStruct* ss)
{
  // static int count = 0;
  // fprintf(stderr, "jitSearchStruct %d\n", ++count);
  _cpJit->initialize();
  _cpJit->emitSearchStruct(ss);
}

void CodeTree::patchAlternative(CodeOp* op)
{
  _cpJit->patchAlternative(op);
}

}