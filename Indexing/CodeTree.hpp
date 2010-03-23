/**
 * @file CodeTree.hpp
 * Defines class for code tree indexes.
 */

#ifndef __CodeTree__
#define __CodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/Portability.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/Vector.hpp"

#include "../Kernel/FlatTerm.hpp"
#include "../Kernel/Term.hpp"

#define LOG_OP(x)
//#define LOG_OP(x) cout<<x<<endl

namespace Indexing
{

using namespace Kernel;
using namespace Lib;

class CodeTree
{
public:
  CodeTree();

  enum Instruction
  {
    SUCCESS = 0,
    CHECK_FUN = 1,
    ASSIGN_VAR = 2,
    CHECK_VAR = 3,
    SUCCESS2 = 4, //this one is here because pointers are guaranted to be only 4-byte aligned
    FAIL = 5,
    NEXT_LIT = 6
  };

  /** Structure containing a single instruction and its arguments */
  struct OpCode
  {
    OpCode() {}
    OpCode(Instruction i) : alternative(0) { info.instr=i; info.arg=0; }
    OpCode(Instruction i, unsigned arg) : alternative(0) { info.instr=i; info.arg=arg; }
    OpCode(void* result) : result(result), alternative(0) { ASS_EQ(instr() & 3, SUCCESS); }

    bool eqModAlt(const OpCode& o) const;

    /**
     * Return true iff OpCode contains a success instruction
     *
     * A succes instruction is either SUCCESS or SUCCESS2, because
     * on some architectures, pointers are only 4-byte aligned and
     * the instruction is stored in first three bits.
     */
    inline bool isSuccess() const { return (instr()&3)==SUCCESS; }

    inline Instruction instr() const { return info.instr; }
    inline void setInstr(Instruction i) { info.instr=i; }

    inline unsigned arg() const { return info.arg; }

#if VDEBUG
    string toString() const;
#endif

    union {
      struct {
        Instruction instr : 3;
        unsigned arg : 29;
      } info;
      void* result;
      size_t data;
    };
    /**
     * Pointer to an alternative operation
     *
     * If nonzero, always points to the first operation of
     * a @b CodeBlock.
     */
    OpCode* alternative;
  };


  /**
   * Backtracking point for the interpretation of the code tree.
   *
   * Invariant:
   * Iff @b tp==tpSpecial, @b op points to a NEXT_LIT operation.
   * Otherwise it points to a first operation in a CodeBlock.
   */
  struct BTPoint
  {
    BTPoint() {}
    BTPoint(size_t tp, OpCode* op) : tp(tp), op(op) {}

    static const size_t tpSpecial=-1;

    /** Position in the flat term */
    size_t tp;
    /** Pointer to the next operation */
    OpCode* op;
  };

  typedef Stack<BTPoint> BTStack;

  /** Context for execution of the code */
  struct EContext
  {
    void init(CodeTree* tree);
    void deinit(CodeTree* tree);
    inline void load(BTPoint bp) { tp=bp.tp; op=bp.op; }
    bool backtrack();

    bool doCheckFun();
    void doAssignVar();
    bool doCheckVar();

    /** true iff the EContext was just initialized */
    bool fresh;
    /** Position in the flat term */
    size_t tp;
    /** Pointer to the next operation */
    OpCode* op;
    /** Flat term to be traversed */
    FlatTerm* ft;
    /** Stack containing backtracking points */
    BTStack btStack;
    /** Variable bindings */
    DArray<TermList> bindings;
  };

  template<class NextLitFn>
  static bool next(EContext& ctx, void*& res, NextLitFn nextLitFun);


  typedef Vector<OpCode> CodeBlock;
  typedef Stack<OpCode> CodeStack;
  typedef DHMap<unsigned,unsigned> VarMap;

  static void compile(Term* t, CodeStack& code, VarMap& varMap, unsigned& nextVarNum);

  static CodeBlock* buildBlock(CodeStack& code, size_t cnt);
  void matchCode(CodeStack& code, size_t& matchedCnt, OpCode*& lastOp);

  void incorporate(CodeStack& code);

  static CodeBlock* firstOpToCodeBlock(OpCode* op);

  template<class NextLitFn, class FoundFn>
  static void remove(EContext& ctx, CodeTree* tree, NextLitFn nextLitFun, FoundFn foundFun);


  /** Maximum number of variables in an inserted term/clause */
  unsigned _maxVarCnt;

#if VDEBUG
  int _initEContextCounter;
#endif

  CodeBlock* _data;
};

class TermCodeTree : public CodeTree
{
public:

  struct TermEContext : public EContext
  {
    void init(TermList t, TermCodeTree* tree);
    void init(Term* t, TermCodeTree* tree);
    void init(FlatTerm* flatTerm, TermCodeTree* tree);
    void deinit(TermCodeTree* tree);

    CLASS_NAME("TermEContext");
    USE_ALLOCATOR(TermEContext);
  private:
    bool _ownFlatTerm;
  };

  void compile(TermList t, CodeStack& code);
  void compile(Term* t, CodeStack& code);

  struct InvOpNextLitFun
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(EContext& ctx)
    {
      INVALID_OPERATION("NEXT_LIT operation should not appear in TermCodeTree");
    }
  };

  static bool next(TermEContext& ctx, void*& res);

};


class ClauseCodeTree : public CodeTree
{
public:

  struct ClauseEContext : public EContext
  {
    void init(Clause* c, ClauseCodeTree* tree);
    void deinit(ClauseCodeTree* tree);

    bool doNextLit();

    CLASS_NAME("ClauseEContext");
    USE_ALLOCATOR(ClauseEContext);

    bool assignNextUnmatchedOrGoBack();

    unsigned _clen;
    /** Index of literal of the indexed clause that is being matched
     *
     * It is a signed integer because we init it to -1 for simplicity.*/
    int _curLitPos;
    DArray<FlatTerm*> _flits;
    /** Indexes of literals of the query clause that match to the first
     * @b _curLitPos+1 literals of the indexed clause */
    DArray<int> _litIndexes;
    /** For each of the query clause literals referenced in the first
     * @b _curLitPos elements of the @b_litIndexes array, is true
     * iff it has a commutative predicate and we can get one more attempt
     * by swapping its arguments */
    DArray<bool> _canReorder;
  };

  void compile(Clause* c, CodeStack& code);

  struct RemovalNextLitFun
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(EContext& ctx0);
  };

  struct ClauseSubsumptionNextLitFun
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(EContext& ctx0);
  };

  static bool next(ClauseEContext& ctx, void*& res);
};

template<class NextLitFn, class FoundFn>
void CodeTree::remove(EContext& ctx, CodeTree* tree, NextLitFn nextLitFun, FoundFn foundFun)
{
  CALL("CodeTree::remove");

  //the remove has to be the first and only thing called on a context
  ASS(ctx.fresh);
  ctx.fresh=false;

  //this is to help us ensure we're looking for variants, not generalizations
  static DHMap<unsigned,unsigned> queryVarBindings;
  queryVarBindings.reset();

  //first op in the current CodeBlock
  static Stack<OpCode*> firstsInBlocks;
  firstsInBlocks.reset();
  firstsInBlocks.push(ctx.op);

  static Stack<unsigned> depthsForLits;


  //in this loop the handlers of ASSIGN_VAR and CHECK_VAR operations are
  //modified so that we look for variants, not for generalisations
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
      if(foundFun(ctx.op->result)) {
	goto found_handler;
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
      if(fte->tag()==FlatTerm::VAR) {
	unsigned qvar=fte->number();
        unsigned* pAsgnVar;
        if(!queryVarBindings.getValuePtr(qvar,pAsgnVar)) {
          if(*pAsgnVar<var) {
            backtrack=true;
            break;
          }
        }
        *pAsgnVar=var;

        ctx.bindings[var]=TermList(qvar,false);
        ctx.tp++;
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
      if(fte->tag()==FlatTerm::VAR) {
        if(ctx.bindings[var]!=TermList(fte->number(),false)) {
          backtrack=true;
          break;
        }
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
      if(ctx.tp!=BTPoint::tpSpecial) {
	depthsForLits.push(firstsInBlocks.size());
      }
      backtrack=!nextLitFun(ctx);
      if(!backtrack) {
      	LOG_OP("nl-alt placed");
      	ctx.btStack.push(BTPoint(BTPoint::tpSpecial, ctx.op));
      }
      else {
	depthsForLits.pop();
      }
      break;
    }
    if(backtrack) {
      if(!ctx.backtrack()) {
	LOG_OP("not found");
	//the element to be removed was not found
	ASSERTION_VIOLATION;
	return;
      }
      if(ctx.tp!=BTPoint::tpSpecial) {
	//we backtracked to the first operation of another block
	firstsInBlocks.push(ctx.op);
      }
      else {
	//we are backtracking somewhere we've been before
	firstsInBlocks.truncate(depthsForLits.top());
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


found_handler:
  ASS(ctx.op->isSuccess());

  OpCode* op0=ctx.op;
  op0->setInstr(CodeTree::FAIL);

  //now let us remove unnecessary instructions and the free memory

  OpCode* op=ctx.op;
  ASS(firstsInBlocks.isNonEmpty());
  OpCode* firstOp=firstsInBlocks.pop();
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
    if(firstsInBlocks.isEmpty()) {
      ASS_EQ(tree->_data,cb);
      tree->_data=alt ? firstOpToCodeBlock(alt) : 0;
      cb->deallocate();
      return;
    }

    //first operation in the CodeBlock that points to the current one (i.e. cb)
    OpCode* prevFirstOp=firstsInBlocks.pop();
    CodeBlock* pcb=firstOpToCodeBlock(prevFirstOp);
    OpCode* prevOp=prevFirstOp;
    //last operatio in the pcb block that cannot be lost
    OpCode* lastPersistent=0;
    //operation that points to the current CodeBlock
    OpCode* pointingOp=0;
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
//      cout<<endl;
//      cout<<"pointingOp:"<<pointingOp->toString()<<endl;
//      cout<<"setting fail on "<<lastPersistent->toString()<<" of "<<endl;
//      cout<<"    "<<pcb->toString()<<endl;
      lastPersistent->setInstr(FAIL);
//      cout<<"res:"<<pcb->toString()<<endl;
    }

    if(lastPersistent) {
      return;
    }

    firstOp=prevFirstOp;
    op=pointingOp;
  }

}


};
#endif /*__CodeTree__*/
