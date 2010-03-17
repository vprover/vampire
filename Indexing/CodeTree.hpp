/**
 * @file CodeTree.hpp
 * Defines class for code tree indexes.
 */

#ifndef __CodeTree__
#define __CodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/Stack.hpp"

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
    SUCCESS2 = 4, //this one is here because pointers are only 4-byte aligned
    FAIL = 5,
    NEXT_LIT = 6
  };

  /** Structure containing a single instruction and its arguments */
  struct OpCode
  {
    OpCode() {}
    OpCode(Instruction i) : alternative(0) { info.instr=i; }
    OpCode(Instruction i, unsigned arg) : alternative(0) { info.instr=i; info.arg=arg; }
    OpCode(void* result) : result(result), alternative(0) { ASS_EQ(instr() & 3, SUCCESS); }

    /** Return true iff @b o is equal to the current object except
     * for the value of the @b alternative field */
    inline bool eqModAlt(const OpCode& o) const { return result==o.result; }

    inline Instruction instr() const { return info.instr; }
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
    };
    OpCode* alternative;
  };


  struct BTPoint
  {
    BTPoint() {}
    BTPoint(size_t tp, OpCode* op) : tp(tp), op(op) {}

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


  typedef Vector<OpCode> CodeBlock;
  typedef Stack<OpCode> CodeStack;
  typedef DHMap<unsigned,unsigned> VarMap;

  static void compile(Term* t, CodeStack& code, VarMap& varMap, unsigned& nextVarNum);

  static CodeBlock* buildBlock(CodeStack& code, size_t cnt);
  void incorporate(CodeStack& code);

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
    void deinit(TermCodeTree* tree);

    CLASS_NAME("TermEContext");
    USE_ALLOCATOR(TermEContext);
  };

  void compile(TermList tl, CodeStack& code);

  static bool next(TermEContext& ctx, void*& res);

  friend class CodeTreeTIS;
};


class ClauseCodeTree : public CodeTree
{
public:
  void compile(Clause* c, CodeStack& code);

};

};
#endif /*__CodeTree__*/
