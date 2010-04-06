/**
 * @file CodeTree_remove.cpp
 * Implements class CodeTree_remove.
 */
/*
#include "../Lib/Recycler.hpp"

#include "CodeTree.hpp"

namespace Indexing
{
using namespace Lib;
using namespace Kernel;

struct CodeTree::RemoverStruct
{
  RemoverStruct(EContext& ctx_, CodeTree* tree_, SuccessDataMatchingFn* successFn_)
  : ctx(ctx_), tree(tree_), successFn(successFn_)
  {
    CALL("CodeTree::RemoverStruct::RemoverStruct");
    ASS(!tree->isEmpty());

    Recycler::get(firstsInBlocks);
    firstsInBlocks->reset();

    Recycler::get(fibDepthsForBt);
    fibDepthsForBt->reset();

    //the remove has to be the first and only thing called on a context
    ASS(ctx.fresh);
    ctx.fresh=false;
  }

  ~RemoverStruct()
  {
    Recycler::release(firstsInBlocks);
    Recycler::release(fibDepthsForBt);
  }

  void perform()
  {
    CALL("CodeTree::RemoverStruct::perform");

    LOG_OP("code tree element removal");

    findRemovingTarget();

    //remove the SUCCESS instruction
    ASS(ctx.op->isSuccess());
    ctx.op->setInstr(CodeTree::FAIL);

    optimizeMemory();
  }

  void findRemovingTarget()
  {
    CALL("CodeTree::RemoverStruct::findRemovingTarget");

    //this is the first operation in the root block
    firstsInBlocks->push(ctx.op);
    ASS(firstOpToCodeBlock(ctx.op)==tree->_data);

    //in this loop the handlers of ASSIGN_VAR and CHECK_VAR operations are
    //modified so that we look for something more general than variants, but
    //not for all generalisations (looking for variants would be better but
    //the check for it would be complicated with backtracking)
    bool backtrack=false;
    for(;;) {
      if(ctx.op->alternative) {
	LOG_OP("alt at "<<ctx.tp);
	ctx.btStack.push(BTPoint(ctx.tp, ctx.op->alternative));
	fibDepthsForBt->push(firstsInBlocks->size());
      }
      LOG_OP(ctx.tp<<':'<<ctx.op->toString());
      switch(ctx.op->instr()) {
      case SUCCESS:
      case SUCCESS2:
	if((*successFn)(ctx.op->result)) {
	  return; //removing target found!
	}
	backtrack=true;
	break;
      case CHECK_FUN:
	backtrack=!ctx.doCheckFun();
	break;
      case ASSIGN_VAR:
      {
	unsigned var=ctx.op->arg();
	const FlatTerm::Entry* fte=&(*ctx.ft)[ctx.tp];
	if(fte->isVar()) {
	  ctx.bindings[var]=TermList(fte->number(),false);
	  ctx.tp++;
	  //if we wanted to look for variants only, here we should have put a check
	  //that we don't assign one query variable into multiple index variables
	}
	else {
	  backtrack=true;
	}
	break;
      }
      case CHECK_VAR:
      {
	unsigned var=ctx.op->arg();
	const FlatTerm::Entry* fte=&(*ctx.ft)[ctx.tp];
	if(fte->isVar(ctx.bindings[var].var())) {
	  ctx.tp++;
	}
	else {
	  backtrack=true;
	}
	break;
      }
      case FAIL:
	backtrack=true;
	break;
      case NEXT_LIT:
	backtrack=!doNextLit();
	break;
      }
      if(backtrack) {
	doBacktrack();
	backtrack=false;
      }
      else {
	//in each CodeBlock there is always either operation SUCCESS or FAIL,
	//so as we haven't encountered one yet, we may safely increase the
	//operation pointer
	ctx.op++;
      }
    }
    //we leave the loop only by a return statement inside
    ASSERTION_VIOLATION;
  }

  bool doNextLit()
  {
    CALL("CodeTree::RemoverStruct::doNextLit");

    //only in ClauseCodeTree a NEXT_LIT instruction can occur
    ClCodeTree::ClauseEContext& cctx=static_cast<ClCodeTree::ClauseEContext&>(ctx);

    bool res=true;

    if(cctx.tp!=BTPoint::tpSpecial) {
      //we are entering a new index clause literal
      //(otherwise we would have landed on the operation
      //by backtracking)

      if(cctx._curLitPos==static_cast<int>(cctx._clen)-1) {
	res=false;
      }
      else {
	cctx._curLitPos++;
	cctx._litIndexes[cctx._curLitPos]=-1;
      }
    }
    if(res) {
      ASS_GE(cctx._curLitPos,0);
      res=cctx.assignNextUnmatchedOrGoBack();
    }
    if(res) {
      LOG_OP("nl-alt placed");
      cctx.btStack.push(BTPoint(BTPoint::tpSpecial, cctx.op));
      fibDepthsForBt->push(firstsInBlocks->size());
    }

    return res;
  }

  void doBacktrack()
  {
    CALL("CodeTree::RemoverStruct::doBacktrack");

    if(!ctx.backtrack()) {
      LOG_OP("not found");
      //the element to be removed was not found
      ASSERTION_VIOLATION;
      INVALID_OPERATION("Attempt to remove a non-existing item from a code tree");
    }
    firstsInBlocks->truncate(fibDepthsForBt->pop());
    if(ctx.tp!=BTPoint::tpSpecial) {
      //we backtracked to the first operation of another block
      firstsInBlocks->push(ctx.op);
    }
    LOG_OP(ctx.tp<<"<-bt");

  }

  void optimizeMemory()
  {
    CALL("CodeTree::RemoverStruct::optimizeMemory");
    LOG_OP("Code tree removal memory optimization");
    LOG_OP("firstsInBlocks->size()="<<firstsInBlocks->size());

    OpCode* op0=ctx.op;

    //now let us remove unnecessary instructions and the free memory

    OpCode* op=ctx.op;
    ASS(firstsInBlocks->isNonEmpty());
    OpCode* firstOp=firstsInBlocks->pop();
    for(;;) {

      while(op>firstOp && !op->alternative) { op--; }

      if(op!=firstOp) {
	ASS(op->alternative);
	//we may only change the instruction, the alternative must remain unchanged
	ASS(op==op0 || !op->isSuccess());
	op->setInstr(CodeTree::FAIL);
	return;
      }
      OpCode* alt=firstOp->alternative;
      CodeBlock* cb=firstOpToCodeBlock(firstOp);
      if(firstsInBlocks->isEmpty()) {
	ASS_EQ(tree->_data,cb);
	tree->_data=alt ? firstOpToCodeBlock(alt) : 0;
	cb->deallocate();
	return;
      }

      //first operation in the CodeBlock that points to the current one (i.e. cb)
      OpCode* prevFirstOp=firstsInBlocks->pop();
      CodeBlock* pcb=firstOpToCodeBlock(prevFirstOp);

      //last operatio in the pcb block that cannot be lost
      OpCode* lastPersistent=0;
      //operation that points to the current CodeBlock
      OpCode* pointingOp=0;

      OpCode* prevOp=prevFirstOp;
      //in how many increases will prevOp become invalid
      size_t prevRem=pcb->length();
      while(prevRem>0) {
	if(prevOp->alternative==firstOp) {
	  ASS_EQ(pointingOp,0);
	  pointingOp=prevOp;
	}

	if((prevOp->alternative && (alt || prevOp->alternative!=firstOp)) || prevOp->isSuccess()) {
	  lastPersistent=prevOp;
	}
	prevOp++;
	prevRem--;
      }
      ASS(pointingOp);
      pointingOp->alternative=alt;

      cb->deallocate();

      if(lastPersistent && lastPersistent<pointingOp && !lastPersistent->isSuccess()) {
	//put the FAIL instruction as early as possible
	lastPersistent->setInstr(FAIL);
      }

      if(lastPersistent) {
        return;
      }

      firstOp=prevFirstOp;
      op=pointingOp;
    }
  }
*/
  /** Stack that contains first op in each CodeBlock on the way to the root */
//  Stack<OpCode*>* firstsInBlocks;

  /** Depths of the firstsInBlocks stack at each backtrack point */
/*  Stack<unsigned>* fibDepthsForBt;

  EContext& ctx;
  CodeTree* tree;
  SuccessDataMatchingFn* successFn;
};

void CodeTree::remove(EContext& ctx, CodeTree* tree, SuccessDataMatchingFn* successFn)
{
  CALL("CodeTree::remove");
  LOG_OP("Code tree item removing");

  RemoverStruct(ctx, tree, successFn).perform();
}


}
*/