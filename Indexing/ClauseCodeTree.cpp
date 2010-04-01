/**
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include "../Lib/BitUtils.hpp"
#include "../Lib/Recycler.hpp"

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


ClauseCodeTree::MatchInfo::MatchInfo(unsigned liIndex, unsigned bindCnt, DArray<TermList>& bindingArray)
: liIndex(liIndex), bindCnt(bindCnt)
{
  size_t bSize=sizeof(TermList)*bindCnt;
  bindings=static_cast<TermList*>(
      ALLOC_KNOWN(bSize, "ClauseCodeTree::MatchInfo::bindings"));
  memcpy(bindings, bindingArray.array(), bSize);
}

ClauseCodeTree::MatchInfo::~MatchInfo()
{
  DEALLOC_KNOWN(bindings, sizeof(TermList)*bindCnt, "ClauseCodeTree::MatchInfo::bindings");
}

ClauseCodeTree::ILStruct::ILStruct(unsigned varCnt, Stack<unsigned>& gvnStack)
: varCnt(varCnt), timestamp(0), matches(0)
{
  size_t gvnSize=sizeof(unsigned)*varCnt;
  globalVarNumbers=static_cast<unsigned*>(
      ALLOC_KNOWN(gvnSize, "ClauseCodeTree::ILStruct::globalVarNumbers"));
  memcpy(globalVarNumbers, gvnStack.begin(), gvnSize);
}

ClauseCodeTree::ILStruct::~ILStruct()
{
  DEALLOC_KNOWN(globalVarNumbers, sizeof(unsigned)*varCnt, "ClauseCodeTree::ILStruct::globalVarNumbers");

  matches->destroy();
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

ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getSuccess(Clause* cl)
{
  CALL("ClauseCodeTree::OpCode::getSuccess");

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

  if(instr()!=o.instr()) {
    return false;
  }
  switch(instr()) {
  case SUCCESS:
  case SUCCESS2:
    return data==o.data;
  case LIT_END:
  case LIT_END2:
    return getILS()->equalsForOpMatching(*o.getILS());
  case CHECK_FUN:
  case CHECK_VAR:
  case ASSIGN_VAR:
    return arg()==o.arg();
  case FAIL:
    return true;
  }
  ASSERTION_VIOLATION;
}

//////////////// auxiliary ////////////////////

ClauseCodeTree::ClauseCodeTree()
: _curTimeStamp(0), _maxVarCnt(0), _entryPoint(0)
{
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

  ILStruct* aux;
  OpCode* lastMatched;
  matchCode(code, startOp, lastMatched, sharedLen, aux);

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
void ClauseCodeTree::matchCode(CodeStack& code, OpCode* startOp, OpCode*& lastAttemptedOp,
    size_t& matchedCnt, ILStruct*& lastILS)
{
  CALL("ClauseCodeTree::matchCode");

  size_t clen=code.length();
  OpCode* treeOp=startOp;

  for(size_t i=0;i<clen;i++) {
    while(!code[i].equalsForOpMatching(*treeOp) && treeOp->alternative) {
      treeOp=treeOp->alternative;
    }
    if(!code[i].equalsForOpMatching(*treeOp)) {
      ASS(!treeOp->alternative);
      matchedCnt=i;
      lastAttemptedOp=treeOp;
      return;
    }

    if(treeOp->isLitEnd()) {
      lastILS=treeOp->getILS();
    }

    //we can safely do increase because as long as we match and something
    //remains in the @b code stack, we aren't at the end of the CodeBlock
    //either (as each code block contains at least one FAIL or SUCCESS
    //operation, and CodeStack contains at most one SUCCESS as the last
    //operation)
    treeOp++;
  }
  //we matched the whole CodeStack
  matchedCnt=clen;
  lastAttemptedOp=treeOp;
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
      ils->previous=prev;
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
    return;
  }

  OpCode* treeOp;
  size_t matchedCnt;
  ILStruct* lastMatchedILS;
  matchCode(code, getEntryPoint(), treeOp, matchedCnt, lastMatchedILS);

  size_t clen=code.length();
  if(clen==matchedCnt) {
    ASS(treeOp->isSuccess());
    //If we are here, we are inserting an item multiple times.
    //We will insert it anyway, because later we may be removing it multiple
    //times as well.
    matchedCnt--;

    //we need to find where to put it
    while(treeOp->alternative) {
      treeOp=treeOp->alternative;
    }
  }

  ASS(!treeOp->alternative);
  CodeBlock* rem=buildBlock(code, clen-matchedCnt, lastMatchedILS);
  treeOp->alternative=&(*rem)[0];
  LOG_OP(rem->toString()<<" incorporated at "<<treeOp->toString()<<" caused by "<<code[matchedCnt].toString());

  code.truncate(matchedCnt);
  while(code.isNonEmpty()) {
    if(code.top().isLitEnd()) {
      delete code.top().getILS();
    }
    code.pop();
  }
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

//////////////// retrieval ////////////////////

void ClauseCodeTree::incTimeStamp()
{
  _curTimeStamp++;
  if(!_curTimeStamp) {
    //handle overflow
    NOT_IMPLEMENTED;
  }
}

void ClauseCodeTree::LiteralMatcher::init(ClauseCodeTree* tree, OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_)
{
  CALL("ClauseCodeTree::LiteralMatcher::init");
  ASS_G(linfoCnt_,0);

  entry=entry_;
  linfos=linfos_;
  linfoCnt=linfoCnt_;

  _fresh=true;
  _matched=false;
  curLInfo=0;
  btStack.reset();
  bindings.ensure(tree->_maxVarCnt);

  ALWAYS(prepareLiteral());
}

/**
 * Try to find a match, and if one is found, return true
 */
bool ClauseCodeTree::LiteralMatcher::next()
{
  CALL("ClauseCodeTree::LiteralMatcher::next");

  if(!_fresh && !_matched) {
    //all possible matches are exhausted
    return false;
  }
  
  if(!execute()) {
    _matched=false;
    return false;
  }

  _matched=true;
  ASS(op->isLitEnd() || op->isSuccess());
  return true;
}

/**
 * Create new MatchInfo structure describing the current match. 
 *
 * It is a responsibility of the caller to delete the returned structure.
 */
ClauseCodeTree::MatchInfo* ClauseCodeTree::LiteralMatcher::createMatchInfo()
{
  CALL("ClauseCodeTree::LiteralMatcher::createMatchInfo");
  ASS(matched());

  ILStruct* ils=op->getILS();
  return new MatchInfo(linfos[curLInfo].litIndex, ils->varCnt, bindings);
}


bool ClauseCodeTree::LiteralMatcher::execute()
{
  CALL("ClauseCodeTree::LiteralMatcher::execute");

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
    case FAIL:
      shouldBacktrack=true;
      break;
    case LIT_END:
    case LIT_END2:
      return true;
    case SUCCESS:
    case SUCCESS2:
      //SUCCESS can only appear as the first operation in a literal block
      ASS_EQ(tp,0);
      return true;
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

  query=query_;
  tree=tree_;
  lms.reset();
  
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
    if((*query)[i]->isEquality()) {
      lInfos[liIndex]=LitInfo::getReversed(lInfos[liIndex]);
      liIndex++;
    }
    liIndex++;
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
      NOT_IMPLEMENTED;
    }
  }
  
  
  return 0;
}

inline bool ClauseCodeTree::ClauseMatcher::litEndAlreadyVisited(OpCode* op)
{
  CALL("ClauseCodeTree::ClauseMatcher::litEndAlreadyVisited");
  ASS(op->isLitEnd());
  
  return op->getILS()->timestamp==tree->_curTimeStamp;
}

void ClauseCodeTree::ClauseMatcher::enterLiteral(OpCode* entry)
{
  CALL("ClauseCodeTree::ClauseMatcher::enterLiteral");
  
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
}


bool ClauseCodeTree::ClauseMatcher::checkCandidate(Clause* cl)
{
  CALL("ClauseCodeTree::ClauseMatcher::checkCandidate");
  
  return false;
}

}









































