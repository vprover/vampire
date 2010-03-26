/**
 * @file CodeTree.cpp
 * Implements class CodeTree for code tree indexes.
 *
 */

#include <stddef.h>

#include "../Lib/Allocator.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Portability.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/TermIterators.hpp"

#if VDEBUG

#include "../Lib/Environment.hpp"
#include "../Kernel/Signature.hpp"

#endif

#include "CodeTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

#if VDEBUG

string CodeTree::OpCode::toString() const
{
  string res;
  switch(instr()) {
  case SUCCESS:
  case SUCCESS2:
    res+="suc";
    break;
  case CHECK_FUN:
    res+="chf:"+Int::toString(arg())+
      ((env.signature->functions()>(int)arg()) ? ("("+env.signature->functionName(arg())+")") : string() );
    break;
  case ASSIGN_VAR:
    res+="asv:"+Int::toString(arg());
    break;
  case CHECK_VAR:
    res+="chv:"+Int::toString(arg());
    break;
  case FAIL:
    res+="fail";
    break;
  case NEXT_LIT:
    res+="nlit";
    break;
  }
  if(alternative) {
    res+="+A";
  }
  return res;
}

#endif

/**
 * Return true iff @b o is equal to the current object except
 * for the value of the @b alternative field
 */
inline bool CodeTree::OpCode::eqModAlt(const OpCode& o) const
{
  if(instr()!=o.instr()) {
    //this works even though SUCCESS and SUCCESS2 are distinct but equivalent
    //(as we would have failed on the result==o.result anyway)
    return false;
  }
  switch(instr()) {
  case SUCCESS:
  case SUCCESS2:
    return result==o.result;
  case CHECK_FUN:
  case ASSIGN_VAR:
  case CHECK_VAR:
    return arg()==o.arg();
  case FAIL:
  case NEXT_LIT:
    return true;
  }
  ASSERTION_VIOLATION;
}

/**
 * Return CodeBlock which contains @b op as its first operation
 */
CodeTree::CodeBlock* CodeTree::firstOpToCodeBlock(OpCode* op)
{
  CALL("CodeTree::firstOpToCodeBlock");

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

CodeTree::CodeTree()
: _maxVarCnt(0),
#if VDEBUG
  _initEContextCounter(0),
#endif
  _data(0)
{
  CALL("CodeTree::CodeTree");
}

void CodeTree::CompileContext::init()
{
  CALL("CodeTree::CompileContext::init");

  nextVarNum=0;
  varMap.reset();
}

void CodeTree::CompileContext::deinit(CodeTree* tree, bool discarded)
{
  CALL("CodeTree::CompileContext::deinit");

  //update the max. number of variables, if necessary
  if(!discarded && nextVarNum>tree->_maxVarCnt) {
    tree->_maxVarCnt=nextVarNum;
  }
}


void CodeTree::compile(Term* t, CodeStack& code, CompileContext& cctx, bool reverseCommutativePredicate)
{
  CALL("CodeTree::compile(Term*...)");

  unsigned func=t->isLiteral() ? static_cast<Literal*>(t)->header() : t->functor();
  code.push(OpCode(CHECK_FUN, func));

  SubtermIterator* sti;

  if(reverseCommutativePredicate) {
    ASS(t->isLiteral());
    ASS(t->commutative());
    sti=new ReversedCommutativeSubtermIterator(static_cast<Literal*>(t));
  }
  else {
    sti=new SubtermIterator(t);
  }

  while(sti->hasNext()) {
    TermList s=sti->next();
    if(s.isVar()) {
      unsigned var=s.var();
      unsigned* varNumPtr;
      if(cctx.varMap.getValuePtr(var,varNumPtr)) {
	*varNumPtr=cctx.nextVarNum++;
	code.push(OpCode(ASSIGN_VAR, *varNumPtr));
      }
      else {
	code.push(OpCode(CHECK_VAR, *varNumPtr));
      }
    }
    else {
      ASS(s.isTerm());
      code.push(OpCode(CHECK_FUN, s.term()->functor()));
    }
  }

  delete sti;
}

/**
 * Build CodeBlock object from the last @b cnt instructions on the
 * @b code stack.
 */
CodeTree::CodeBlock* CodeTree::buildBlock(CodeStack& code, size_t cnt)
{
  CALL("CodeTree::buildBlock");

  size_t clen=code.length();
  ASS_LE(cnt,clen);

  CodeBlock* res=CodeBlock::allocate(cnt);
  size_t sOfs=clen-cnt;
  for(size_t i=0;i<cnt;i++) {
    ASS_EQ(code[i+sOfs].alternative,0); //the ops should not have an alternattive set yet
    (*res)[i]=code[i+sOfs];
  }
  return res;
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
void CodeTree::matchCode(CodeStack& code, OpCode* startOp, OpCode*& lastAttemptedOp, size_t& matchedCnt)
{
  CALL("CodeTree::matchCode");

  size_t clen=code.length();
  OpCode* treeOp=startOp;

  for(size_t i=0;i<clen;i++) {
    while(!code[i].eqModAlt(*treeOp) && treeOp->alternative) {
      treeOp=treeOp->alternative;
    }
    if(!code[i].eqModAlt(*treeOp)) {
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

void CodeTree::incorporate(CodeStack& code)
{
  CALL("CodeTree::incorporate");
  ASS(code.top().isSuccess());

  if(isEmpty()) {
    _data=buildBlock(code, code.length());
    return;
  }

  OpCode* treeOp;
  size_t matchedCnt;
  matchCode(code, getEntryPoint(), treeOp, matchedCnt);

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
  CodeBlock* rem=buildBlock(code, clen-matchedCnt);
  treeOp->alternative=&(*rem)[0];
  LOG_OP(rem->toString()<<" incorporated at "<<treeOp->toString()<<" caused by "<<code[matchedCnt].toString());
}

void CodeTree::EContext::init(CodeTree* tree)
{
  CALL("CodeTree::EContext::init");
  ASS(!tree->isEmpty()); //the tree must already contain something

#if VDEBUG
  tree->_initEContextCounter++;
#endif

  fresh=true;
  tp=0;
  op=tree->getEntryPoint();
  btStack.reset();
  bindings.ensure(tree->_maxVarCnt);

}

void CodeTree::EContext::deinit(CodeTree* tree)
{
  CALL("CodeTree::EContext::deinit");

#if VDEBUG
  ASS_G(tree->_initEContextCounter,0);
  tree->_initEContextCounter--;
#endif
}

bool CodeTree::EContext::backtrack()
{
  if(btStack.isEmpty()) {
    return false;
  }
  load(btStack.pop());
  return true;
}

bool CodeTree::EContext::doCheckFun()
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

void CodeTree::EContext::doAssignVar()
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

bool CodeTree::EContext::doCheckVar()
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

/**
 * Perform the operations of the code tree until a SUCCESS
 * operation is reached or the end of the code is reached
 *
 * The @b NextLitFn is a functor corresponding to a function
 *
 * bool nextLitFun(EContext& ctx)
 *
 * that handles the NEXT_LIT operation and returns false in
 * case it was unsuccessful and we should backtrack.
 */
template<class NextLitFn>
bool CodeTree::next(EContext& ctx, void*& res, NextLitFn nextLitFun)
{
  CALL("CodeTree::next");

  if(!ctx.fresh) {
    //we backtrack from what we found in the previous run
    if(!ctx.backtrack()) {
      return false;
    }
  }

  ctx.fresh=false;

  bool backtrack=false;
  for(;;) {
    if(ctx.op->alternative) {
      LOG_OP("alt at "<<ctx.tp);
      ctx.btStack.push(BTPoint(ctx.tp, ctx.op->alternative));
    }
    LOG_OP(ctx.tp<<':'<<ctx.op->toString());
    switch(ctx.op->instr()) {
    case SUCCESS:
    case SUCCESS2:
      res=ctx.op->result;
      return true;
    case CHECK_FUN:
      backtrack=!ctx.doCheckFun();
      break;
    case ASSIGN_VAR:
      ctx.doAssignVar();
      break;
    case CHECK_VAR:
      backtrack=!ctx.doCheckVar();
      break;
    case FAIL:
      backtrack=true;
      break;
    case NEXT_LIT:
      backtrack=!nextLitFun(ctx);
      if(!backtrack) {
      	LOG_OP("nl-alt placed");
      	ctx.btStack.push(BTPoint(BTPoint::tpSpecial, ctx.op));
      }
      break;
    }
    if(backtrack) {
      if(!ctx.backtrack()) {
	LOG_OP("not found");
	return false;
      }
      LOG_OP(ctx.tp<<"<-bt");
      backtrack=false;
    }
    else {
      //in each CodeBlock there is always either operation SUCCESS or FAIL,
      //so as we haven't encountered one yet, we may safely increase the
      //operation pointer
      ctx.op++;
    }
  }
}


/////////////////////////

void TermCodeTree::compile(TermList t, CodeStack& code)
{
  CALL("TermCodeTree::compile(TermList...)");

  if(t.isVar()) {
    code.push(OpCode(ASSIGN_VAR, 0));
    if(_maxVarCnt==0) {
      _maxVarCnt=1;
    }
  }
  else {
    static CompileContext cctx;
    cctx.init();

    CodeTree::compile(t.term(), code, cctx);

    cctx.deinit(this);
  }
  code.push(OpCode(SUCCESS));
}

void TermCodeTree::compile(Term* t, CodeStack& code)
{
  CALL("TermCodeTree::compile(TermList...)");

  static CompileContext cctx;
  cctx.init();

  CodeTree::compile(t, code, cctx);
  code.push(OpCode(SUCCESS));

  cctx.deinit(this);
}

void TermCodeTree::TermEContext::init(TermList t, TermCodeTree* tree)
{
  CALL("TermCodeTree::TermEContext::init(TermList...)");

  EContext::init(tree);

  ft=FlatTerm::create(t);
  _ownFlatTerm=true;
}

void TermCodeTree::TermEContext::init(Term* t, TermCodeTree* tree)
{
  CALL("TermCodeTree::TermEContext::init(Term*...)");

  EContext::init(tree);

  ft=FlatTerm::create(t);
  _ownFlatTerm=true;
}

void TermCodeTree::TermEContext::init(FlatTerm* flatTerm, TermCodeTree* tree)
{
  CALL("TermCodeTree::TermEContext::init(FlatTerm*...)");

  EContext::init(tree);

  ft=flatTerm;
  _ownFlatTerm=false;
}

void TermCodeTree::TermEContext::deinit(TermCodeTree* tree)
{
  CALL("TermCodeTree::TermEContext::deinit");

  if(_ownFlatTerm) {
    ft->destroy();
  }

  EContext::deinit(tree);
}


/**
 * Perform the operations of the code tree until a SUCCESS
 * operation is reached or the end of the code is reached
 */
bool TermCodeTree::next(TermEContext& ctx, void*& res)
{
  CALL("TermCodeTree::next");

  return CodeTree::next(ctx,res,InvOpNextLitFun());
}


/////////////////////////

/**
 * Compares literals based on which one is easier to find a
 * match for.
 */
struct LiteralMatchabilityComparator
{
  Comparison compare(Literal* l1, Literal* l2)
  {
    unsigned l1Num=l1->header();
    unsigned l2Num=l2->header();
    Comparison res=Int::compare(l2Num,l1Num);
    if(res!=EQUAL) { return res; }

    l1Num=l1->weight() - l1->getDistinctVars();
    l2Num=l2->weight() - l2->getDistinctVars();
    return Int::compare(l2Num,l1Num);
  }
};

void ClauseCodeTree::evalSharing(Literal* lit, OpCode* startOp, size_t& sharedLen, size_t& unsharedLen)
{
  CALL("ClauseCodeTree::evalSharing");

  static CodeStack code;
  static CompileContext cctx;

  code.reset();
  cctx.init();

  compileLiteral(lit, code, cctx);

  cctx.deinit(this, true);

  OpCode* lastMatched;
  matchCode(code, startOp, lastMatched, sharedLen);

  unsharedLen=code.size()-sharedLen;
}

void ClauseCodeTree::compileLiteral(Literal* lit, CodeStack& code, CompileContext& cctx)
{
  CALL("ClauseCodeTree::compileLiteral");

  code.push(OpCode(NEXT_LIT));
  CodeTree::compile(lit, code, cctx);
}

void ClauseCodeTree::compile(Clause* c, CodeStack& code)
{
  CALL("ClauseCodeTree::compile(Clause*...)");

  unsigned clen=c->length();
  static DArray<Literal*> lits;
  lits.initFromArray(clen, *c);

  if(!isEmpty() && clen>1) {
    lits.sort(LiteralMatchabilityComparator());

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

//  if(clen>1) {
//    swap(lits[0],lits[clen-1]);
//  }
//  lits.sort(LiteralMatchabilityComparator());
//  lits.sortInversed(LiteralMatchabilityComparator());

  static CompileContext cctx;
  cctx.init();

  for(unsigned i=0;i<clen;i++) {
    compileLiteral(lits[i], code, cctx);
  }
  code.push(OpCode(SUCCESS));

  cctx.deinit(this);
}

void ClauseCodeTree::ClauseEContext::init(Clause* cl, ClauseCodeTree* tree)
{
  CALL("ClauseCodeTree::ClauseEContext::init");

  EContext::init(tree);

  _clen=cl->length();
  _curLitPos=-1;
  _flits.ensure(_clen);
  //this array's elements correspont to literals of indexed clause,
  //but we reject indexed clauses that are longer that the query clause
  _litIndexes.ensure(_clen);
  _canReorder.ensure(_clen);
  for(unsigned i=0;i<_clen;i++) {
    _flits[i]=FlatTerm::create((*cl)[i]);
  }
}

void ClauseCodeTree::ClauseEContext::deinit(ClauseCodeTree* tree)
{
  CALL("ClauseCodeTree::ClauseEContext::deinit");

  for(unsigned i=0;i<_clen;i++) {
    _flits[i]->destroy();
  }

  EContext::deinit(tree);
}

/**
 * Move to the next query literal that isn't already matched to an
 * index literal with lower number. If successful, return true.
 * Otherwise move back to the previous index literal and return false.
 */
bool ClauseCodeTree::ClauseEContext::assignNextUnmatchedOrGoBack()
{
  CALL("ClauseCodeTree::ClauseEContext::assignNextUnmatchedOrGoBack");

  int newIndex=_litIndexes[_curLitPos]+1;
  //make sure we perform a multi-set subsumption check
  bool passed;
  do {
    passed=true;
    if(newIndex>=static_cast<int>(_clen)) {
      //there is no next unmatched query literal, we must go back
      //by one index literal
      _curLitPos--;
      if(_curLitPos!=-1) {
  	ft=_flits[_litIndexes[_curLitPos]];
      }
      //there is no need to set the @b tp position, as we'll backtrack
      //to it as soon as we get to the main interpreter loop
      return false;
    }
    for(int i=0;i<_curLitPos;i++) {
      if(_litIndexes[i]==newIndex) {
	newIndex++;
	passed=false;
	break;
      }
    }
  } while(!passed);

  _litIndexes[_curLitPos]=newIndex;

  ft=_flits[newIndex];
  tp=0;
  return true;
}

bool ClauseCodeTree::ClauseSubsumptionNextLitFun::operator()(EContext& ctx0)
{
  CALL("ClauseCodeTree::ClauseSubsumptionNextLitFun::operator()");
  ASS_EQ(ctx0.op->instr(), NEXT_LIT);

  ClauseEContext& ctx=static_cast<ClauseEContext&>(ctx0);

  //marks whether we have landed on the operation by backtracking
  //or we are entering a new index literal after succesfully matching
  //the previous one
  bool cameFromBacktrack=ctx.tp==BTPoint::tpSpecial;

  if(cameFromBacktrack && ctx._canReorder[ctx._curLitPos]) {
    ASS_GE(ctx._curLitPos,0);
    //we can swap arguments of a commutative predicate and try again
    ctx.ft->swapCommutativePredicateArguments();
    ctx._canReorder[ctx._curLitPos]=false;
    ctx.tp=0;
    return true;
  }

  if(!cameFromBacktrack) {
    //we are entering a new index clause literal
    if(ctx._curLitPos==static_cast<int>(ctx._clen)-1) {
      //unless the index clause has more literals than the query clause
      return false;
    }
    ctx._curLitPos++;
    ctx._litIndexes[ctx._curLitPos]=-1;
  }
  ASS_GE(ctx._curLitPos,0);

  if(!ctx.assignNextUnmatchedOrGoBack()) {
    return false;
  }

  //we are dealing with literals, so the first element in the flatterm must be
  //FUN (not a variable)
  ASS_EQ((*ctx.ft)[0].tag(), FlatTerm::FUN);
  //mark commutative predicates so we can later swap their arguments
  //(as for now, only the equality is commutative)
  ctx._canReorder[ctx._curLitPos]= ((*ctx.ft)[0].number()|1) == 1;

  return true;
}

bool ClauseCodeTree::next(ClauseEContext& ctx, void*& res)
{
  CALL("ClauseCodeTree::next");

  return CodeTree::next(ctx,res,ClauseSubsumptionNextLitFun());
}

}












































