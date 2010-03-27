/**
 * @file ClauseCodeTree.cpp
 * Implements class ClauseCodeTree.
 */

#include "../Lib/BitUtils.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#include "ClauseCodeTree.hpp"

namespace Indexing
{

ClauseCodeTree::ClauseCodeTree()
: _maxVarCnt(0), _entryPoint(0)
{
}

ClauseCodeTree::ILStruct::ILStruct(ILStruct* previous, unsigned varCnt, Stack<unsigned>& gvnStack)
: previous(previous), varCnt(varCnt), timestamp(0)
{
  size_t gvnSize=sizeof(unsigned)*varCnt;
  globalVarNumbers=static_cast<unsigned*>(
      ALLOC_KNOWN(gvnSize, "ClauseCodeTree::ILStruct::globalVarNumbers"));
  memcpy(globalVarNumbers, gvnStack.begin(), sizeof(unsigned)*varCnt);
}

ClauseCodeTree::ILStruct::~ILStruct()
{
  DEALLOC_KNOWN(globalVarNumbers, sizeof(unsigned)*varCnt, "ClauseCodeTree::ILStruct::globalVarNumbers");
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
ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getCheckOp(Instruction i, unsigned num)
{
  CALL("ClauseCodeTree::OpCode::getCheckOp");
  ASS(i==CHECK_FUN || i==CHECK_VAR);

  OpCode res;
  res.alternative=0;
  res.info.instr=i;
  res.info.arg=num;
  return res;
}
ClauseCodeTree::OpCode ClauseCodeTree::OpCode::getAssignVar()
{
  CALL("ClauseCodeTree::OpCode::getAssignVar");

  OpCode res;
  res.alternative=0;
  res.info.instr=ASSIGN_VAR;
  return res;
}

/**
 * Return true iff @b o is equal to the current object except
 * for the value of the @b alternative field
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
    return arg()==o.arg();
  case ASSIGN_VAR:
  case FAIL:
    return true;
  }
  ASSERTION_VIOLATION;
}


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

  OpCode* lastMatched;
  matchCode(code, startOp, lastMatched, sharedLen);

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
void ClauseCodeTree::matchCode(CodeStack& code, OpCode* startOp, OpCode*& lastAttemptedOp, size_t& matchedCnt)
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

  ILStruct* prevILS=0;
  if(addLitEnd && code.isNonEmpty()) {
    //the previous operation on the stack (if any) has to be a LIT_END of the previous literal
    ASS(code.top().isLitEnd());
    prevILS=code.top().getILS();
  }

  static Stack<unsigned> globalCounterparts;
  globalCounterparts.reset();

  cctx.nextLit();

  code.push(OpCode::getCheckOp(CHECK_FUN, lit->header()));

  SubtermIterator sti(lit);

  while(sti.hasNext()) {
    TermList s=sti.next();
    if(s.isVar()) {
      unsigned var=s.var();
      unsigned* varNumPtr;
      if(cctx.varMap.getValuePtr(var,varNumPtr)) {
	*varNumPtr=cctx.nextVarNum++;
	code.push(OpCode::getAssignVar());

	if(addLitEnd) {
	  unsigned* globalVarNumPtr;
	  if(cctx.globalVarMap.getValuePtr(var,globalVarNumPtr)) {
	    *globalVarNumPtr=cctx.nextGlobalVarNum++;
	  }
	  globalCounterparts.push(*globalVarNumPtr);
	}
      }
      else {
	code.push(OpCode::getCheckOp(CHECK_VAR, *varNumPtr));
      }
    }
    else {
      ASS(s.isTerm());
      code.push(OpCode::getCheckOp(CHECK_FUN, s.term()->functor()));
    }
  }

  if(addLitEnd) {
    unsigned varCnt=cctx.nextVarNum;
    ASS_EQ(varCnt, globalCounterparts.size());
    ILStruct* ils=new ILStruct(prevILS, varCnt, globalCounterparts);
    code.push(OpCode::getLitEnd(ils));
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

  NOT_IMPLEMENTED;
}

}
