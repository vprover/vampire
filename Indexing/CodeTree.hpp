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
#include "../Lib/Stack.hpp"
#include "../Lib/Vector.hpp"

#include "../Kernel/FlatTerm.hpp"
#include "../Kernel/Term.hpp"

#if VDEBUG
#include "../Lib/TimeCounter.hpp"
#endif

#define LOG_OP(x)
//#define LOG_OP(x) cout<<x<<endl
//#define LOG_OP(x) if(TimeCounter::isBeingMeasured(TC_FORWARD_SUBSUMPTION)) { cout<<x<<endl; }

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
    OpCode(void* result) : result(result), alternative(0) { ASS(isSuccess()); }

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

  /** Context for code compilation */
  struct CompileContext
  {
    void init();
    void deinit(CodeTree* tree, bool discarded=false);

    unsigned nextVarNum;
    VarMap varMap;
  };

  struct SuccessDataMatchingFn
  {
    virtual ~SuccessDataMatchingFn() {}

    virtual bool operator()(void* data) = 0;
  };

  static void compile(Term* t, CodeStack& code, CompileContext& cctx, bool reverseCommutativePredicate=false);

  static CodeBlock* firstOpToCodeBlock(OpCode* op);
  static CodeBlock* buildBlock(CodeStack& code, size_t cnt);

  static void matchCode(CodeStack& code, OpCode* startOp, OpCode*& lastAttemptedOp, size_t& matchedCnt);

  void incorporate(CodeStack& code);

  struct RemoverStruct;
  static void remove(EContext& ctx, CodeTree* tree, SuccessDataMatchingFn* successFn);

  inline bool isEmpty() { return !_data; }
  inline OpCode* getEntryPoint() { ASS(!isEmpty()); return &(*_data)[0]; }

  template<class Visitor>
  void visitAllOps(Visitor visitor);

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


class ClCodeTree : public CodeTree
{
public:

  struct ClauseEContext : public EContext
  {
    void init(Clause* c, ClCodeTree* tree);
    void deinit(ClCodeTree* tree);

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

  void evalSharing(Literal* lit, OpCode* startOp, size_t& sharedLen, size_t& unsharedLen);

  static void compileLiteral(Literal* lit, CodeStack& code, CompileContext& cctx);

  void compile(Clause* c, CodeStack& code);

  struct ClauseSubsumptionNextLitFun
  {
    DECL_RETURN_TYPE(bool);
    bool operator()(EContext& ctx0);
  };

  static bool next(ClauseEContext& ctx, void*& res);
};

template<class Visitor>
void CodeTree::visitAllOps(Visitor visitor)
{
  CALL("CodeTree::visitAllOps");

  static Stack<CodeBlock*> blocks;
  blocks.reset();

  if(_data) { blocks.push(_data); }

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


};
#endif /*__CodeTree__*/
