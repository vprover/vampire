/**
 * @file CodeTree.hpp
 * Defines class CodeTree.
 */

#ifndef __CodeTree__
#define __CodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/TriangularArray.hpp"
#include "../Lib/Vector.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "Index.hpp"


#define LOG_OP(x)
//#define LOG_OP(x) cout<<x<<endl
//#define LOG_OP(x) if(TimeCounter::isBeingMeasured(TC_FORWARD_SUBSUMPTION)) { cout<<x<<endl; }

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class CodeTree
{
public:
  CodeTree();

public:

  struct ILStruct;
  struct SearchStruct;

  struct LitInfo
  {
    LitInfo() {}
    LitInfo(Clause* cl, unsigned litIndex);
    void dispose();

    static LitInfo getReversed(const LitInfo& li);
    static LitInfo getOpposite(const LitInfo& li);

    /** Index of this LitInfo in the ClauseMatcher object */
    unsigned liIndex;
    /** Index of the literal in the query clause */
    unsigned litIndex;
    FlatTerm* ft;
    bool opposite;
  };

  struct MatchInfo
  {
    MatchInfo(ILStruct* ils, unsigned liIndex, DArray<TermList>& bindingArray);
    ~MatchInfo();

    CLASS_NAME("CodeTree::MatchInfo");
    USE_ALLOCATOR(MatchInfo);

    /** Index of the matched LitInfo in the EContext */
    unsigned liIndex;
    /** this is redundant and is present here just so that the object
     * can be conveniently destroyed */
    unsigned bindCnt;
    /** array of bindings */
    TermList* bindings;
  };
  
  typedef Stack<MatchInfo*> MatchStack;

  /**
   * Structure with information about an indexed literal
   */
  struct ILStruct
  {
    ILStruct(unsigned varCnt, Stack<unsigned>& gvnStack);
    ~ILStruct();
    void putIntoSequence(ILStruct* previous_);

    bool equalsForOpMatching(const ILStruct& o) const;
    
    void disposeMatches();

    CLASS_NAME("CodeTree::ILStruct");
    USE_ALLOCATOR(ILStruct);

    struct GVArrComparator;
    
    unsigned depth;
    ILStruct* previous;
    unsigned varCnt;
    unsigned* globalVarNumbers;

    unsigned* sortedGlobalVarNumbers;
    
    /** Permutation that should be applied to bindings so that they will
     *  correspond to the sortedGlobalVarNumbers */
    unsigned* globalVarPermutation;
    
    unsigned timestamp;
    //from here on, the values are valid only if the timestamp is current
    MatchStack matches;
    /** all possible lits were tried to match */
    bool visited;
    bool finished;
  };

  enum Instruction
  {
    //it means fail if data==0
    SUCCESS_OR_FAIL = 0,
    SUCCESS2 = 4, //this one is here because pointers are guaranted to be only 4-byte aligned
    LIT_END = 1,
    LIT_END2 = 5, //this one also
    CHECK_FUN = 2,
    ASSIGN_VAR = 3,
    CHECK_VAR = 6,
    SEARCH_STRUCT = 7
  };

  /** Structure containing a single instruction and its arguments */
  struct OpCode
  {
    static OpCode getSuccess(void* data);
    static OpCode getLitEnd(ILStruct* ils);
    static OpCode getTermOp(Instruction i, unsigned num);

    void makeFail() { data=0; }
    
    bool equalsForOpMatching(const OpCode& o) const;

    /**
     * Return true iff OpCode contains a success instruction
     *
     * A succes instruction is either SUCCESS or SUCCESS2, because
     * on some architectures, pointers are only 4-byte aligned and
     * the instruction is stored in first three bits.
     */
    inline bool isSuccess() const { return (instr()&3)==SUCCESS_OR_FAIL && data; }
    inline bool isFail() const { return !data; }
    inline bool isLitEnd() const { return (instr()&3)==LIT_END; }
    inline bool isSearchStruct() const { return instr()==SEARCH_STRUCT; }
    inline bool isCheckFun() const { return instr()==CHECK_FUN; }

    inline void* getSuccessResult() { ASS(isSuccess()); return result; }
    
    inline ILStruct* getILS()
    {
      ASS(isLitEnd());
      return reinterpret_cast<ILStruct*>(data&~static_cast<size_t>(LIT_END));
    }
    inline const ILStruct* getILS() const
    {
      return const_cast<OpCode*>(this)->getILS();
    }
    
    SearchStruct* getSearchStruct();

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
  
  struct SearchStruct
  {
    SearchStruct(size_t length);
    ~SearchStruct();
    OpCode*& targetOp(unsigned fn);

    CLASS_NAME("CodeTree::SearchStruct");
    USE_ALLOCATOR(SearchStruct);
    
    struct OpComparator;

    OpCode landingOp;
    size_t length;
    unsigned* values;
    OpCode** targets;
  };


  typedef Vector<OpCode> CodeBlock;
  typedef Stack<OpCode> CodeStack;

  //////// auxiliary methods //////////

  inline bool isEmpty() { return !_entryPoint; }
  inline OpCode* getEntryPoint() { ASS(!isEmpty()); return &(*_entryPoint)[0]; }
  static CodeBlock* firstOpToCodeBlock(OpCode* op);

  template<class Visitor>
  void visitAllOps(Visitor visitor);

  //////////// insertion //////////////

  typedef DHMap<unsigned,unsigned> VarMap;

  /** Context for code compilation */
  struct CompileContext
  {
    void init();
    void deinit(CodeTree* tree, bool discarded=false);

    void nextLit();

    unsigned nextVarNum;
    unsigned nextGlobalVarNum;
    VarMap varMap;
    VarMap globalVarMap;
  };

  static CodeBlock* buildBlock(CodeStack& code, size_t cnt, ILStruct* prev);
  void incorporate(CodeStack& code);
  
  void compressCheckFnOps(OpCode* chainStart);

  static void compileTerm(Term* trm, CodeStack& code, CompileContext& cctx, bool addLitEnd);

  //////////// removal //////////////

  void optimizeMemoryAfterRemoval(Stack<OpCode*>* firstsInBlocks, OpCode* removedOp);

  struct RemovingMatcher
  {
  public:
    bool next();
    
    OpCode* op;
  protected:
    void init(OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_,
	CodeTree* tree_, Stack<OpCode*>* firstsInBlocks_);


    bool prepareLiteral();
    bool backtrack();
    bool doSearchStruct();
    bool doCheckFun();
    bool doAssignVar();
    bool doCheckVar();
    
  
    struct BTPoint
    {
      BTPoint(size_t tp, OpCode* op, size_t fibDepth)
      : tp(tp), op(op), fibDepth(fibDepth) {}
      
      size_t tp;
      OpCode* op;
      size_t fibDepth;
    };
  
    size_t tp;
    FlatTerm* ft;
    /** Variable bindings */
    DArray<unsigned> bindings;
    
    Stack<BTPoint> btStack;
    Stack<OpCode*>* firstsInBlocks;
    bool fresh;
    size_t curLInfo;
    
    OpCode* entry;
    size_t initFIBDepth;
    
    LitInfo* linfos;
    size_t linfoCnt;
    
    bool matchingClauses;
    CodeTree* tree;
  };
  
  //////// retrieval //////////

  /**
   * Backtracking point for the interpretation of the code tree.
   */
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
  typedef DArray<TermList> BindingArray;

  /**
   * Context for finding matches of literals
   *
   * Here the actual execution of the code of the tree takes place.
   *
   * The object is not initialized not only by constructor, but also by 
   * a call to the @b init function (inheritors should implement their 
   * own @b init function (possibly with other arguments) that will call 
   * this one. After use, the @b deinit function should be called (if 
   * present). This allows for reuse of a single object.
   */
  struct Matcher
  {
    void init(CodeTree* tree, OpCode* entry_);
    
    inline bool finished() const { return !_fresh && !_matched; }
    inline bool matched() const { return _matched && op->isLitEnd(); }
    inline bool success() const { return _matched && op->isSuccess(); }



  private:
    bool backtrack();
    bool doSearchStruct();
    bool doCheckFun();
    void doAssignVar();
    bool doCheckVar();

  protected:
    bool execute();
    bool prepareLiteral();

  public:
    /**
     * Pointer to the current operation
     *
     * Must be initialized by inheritor (either directly or by 
     * a call to the @b prepareLiteral function).
     */
    OpCode* op;
    /** Variable bindings */
    BindingArray bindings;
    
  protected:
    bool _fresh;
    bool _matched;

    /**
     * Position in the flat term
     *
     * Must be initialized by inheritor (either directly or by 
     * a call to the @b prepareLiteral function).
     */
    size_t tp;
    /**
     * Flat term to be traversed
     *
     * Must be initialized by inheritor (either directly or by 
     * a call to the @b prepareLiteral function).
     */
    FlatTerm* ft;
    /** Stack containing backtracking points */
    BTStack btStack;

    OpCode* entry;
    
    CodeTree* tree;
    /**
     * Array of alternative LitInfo objects
     *
     * Must be initialized by inheritor.
     */
    LitInfo* linfos;
    /**
     * Length of the @b linfos array
     *
     * Must be initialized by inheritor.
     */
    size_t linfoCnt;

    /**
     * Currently matched LitInfo object in case LitInfo objects 
     * are used (they are not in TermCodeTree::TermMatcher).
     */
    size_t curLInfo;

  };


  void incTimeStamp();

  //////// member variables //////////
  

  bool _clauseCodeTree;
  unsigned _curTimeStamp;
  
  /** maximal number of local variables in a stored term/literal (always at least 1) */
  unsigned _maxVarCnt;

  CodeBlock* _entryPoint;
  
};

}

#endif // __CodeTree__

