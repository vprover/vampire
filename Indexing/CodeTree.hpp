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
 * @file CodeTree.hpp
 * Defines class CodeTree.
 */

#ifndef __CodeTree__
#define __CodeTree__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Hash.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TriangularArray.hpp"
#include "Lib/Vector.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/FlatTerm.hpp"

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
  struct ILStruct;
  struct SearchStruct;
  struct CodeOp;
  
protected:  
  /**
  * During the destruction of the CodeTree,
  * onCodeOpDestroying is called on each CodeOp
  * as an opportunity to release dynamically
  * allocated memory "owned" by the particular CodeOp
  * (the details are expected to be descendant specific)
  */
  void (*_onCodeOpDestroying)(CodeOp* op);
      
public:
  CodeTree();
  ~CodeTree();
  
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
    /** Index of the matched LitInfo in the EContext */
    unsigned liIndex;
    /** array of bindings */
    TermList bindings[1];

  private:
    void init(ILStruct* ils, unsigned liIndex, DArray<TermList>& bindingArray);

    static MatchInfo* alloc(unsigned bindCnt);

    void destroy(unsigned bindCnt);


    friend struct ILStruct;

    //these functions are undefined as we take care of the MatchInfo initialisation
    //and destruction ourselves
    MatchInfo();
    ~MatchInfo();
    void operator delete(void*);
    void* operator new(size_t,unsigned length);
  };

  /**
   * Structure with information about an indexed literal
   */
  struct ILStruct
  {
    ILStruct(Literal* lit, unsigned varCnt, Stack<unsigned>& gvnStack);
    ~ILStruct();
    void putIntoSequence(ILStruct* previous_);

    bool equalsForOpMatching(const ILStruct& o) const;

    void ensureFreshness(unsigned globalTimestamp);

    CLASS_NAME(CodeTree::ILStruct);
    USE_ALLOCATOR(ILStruct);

    struct GVArrComparator;

    unsigned depth;
    ILStruct* previous;

    unsigned isVarEqLit:1;
    unsigned varCnt:31;

    TermList varEqLitSort; // at least in the non-polymorphic case a (64-bit) TermList could be replaced by a (32-bit) unsigned sort.term()->getId()

    unsigned* globalVarNumbers;

    unsigned* sortedGlobalVarNumbers;

    /** Permutation that should be applied to bindings so that they will
     *  correspond to the sortedGlobalVarNumbers */
    unsigned* globalVarPermutation;

    unsigned timestamp;
    //from here on, the values are valid only if the timestamp is current

    void addMatch(unsigned liIndex, DArray<TermList>& bindingArray);
    void deleteMatch(unsigned matchIndex);
    MatchInfo*& getMatch(unsigned matchIndex);

    unsigned matchCnt;

    /** all possible lits were tried to match */
    bool visited;
    bool finished;
    bool noNonOppositeMatches;
  private:
    DArray<MatchInfo*> matches;
  };

  enum InstructionPrefix
  {
    //it means fail if data==0
    SUCCESS_OR_FAIL = 0,
    CHECK_GROUND_TERM = 1,
    LIT_END = 2,
    /** One of instructions that are determined by the instruction suffix */
    SUFFIX_INSTR = 3
  };
  enum InstructionSuffix
  {
    CHECK_FUN = 0,
    ASSIGN_VAR = 1,
    CHECK_VAR = 2,
    SEARCH_STRUCT = 3
  };

  /** Structure containing a single instruction and its arguments */
  struct CodeOp
  {
    static CodeOp getSuccess(void* data);
    static CodeOp getLitEnd(ILStruct* ils);
    static CodeOp getTermOp(InstructionSuffix i, unsigned num);
    static CodeOp getGroundTermCheck(Term* trm);

    bool equalsForOpMatching(const CodeOp& o) const;

    /**
     * Return true iff CodeOp contains a success instruction
     *
     * A success instruction is either SUCCESS or SUCCESS2, because
     * on some architectures, pointers are only 4-byte aligned and
     * the instruction is stored in first three bits.
     */
    inline bool isSuccess() const { return instrPrefix()==SUCCESS_OR_FAIL && data(); }
    inline bool isFail() const { return !data(); }
    inline bool isLitEnd() const { return instrPrefix()==LIT_END; }
    inline bool isSearchStruct() const { return instrPrefix()==SUFFIX_INSTR && instrSuffix()==SEARCH_STRUCT; }
    inline bool isCheckFun() const { return instrPrefix()==SUFFIX_INSTR && instrSuffix()==CHECK_FUN; }
    inline bool isCheckGroundTerm() const { return instrPrefix()==CHECK_GROUND_TERM; }

    inline Term* getTargetTerm() const
    {
      ASS(isCheckGroundTerm());
      return reinterpret_cast<Term*>(data()&~static_cast<size_t>(CHECK_GROUND_TERM));
    }

    inline void* getSuccessResult() { ASS(isSuccess()); return _result; }

    inline ILStruct* getILS()
    {
      ASS(isLitEnd());
      return reinterpret_cast<ILStruct*>(data()&~static_cast<size_t>(LIT_END));
    }
    inline const ILStruct* getILS() const
    {
      return const_cast<CodeOp*>(this)->getILS();
    }

    SearchStruct* getSearchStruct();

    inline InstructionPrefix instrPrefix() const { return static_cast<InstructionPrefix>(_info.prefix); }
    inline InstructionSuffix instrSuffix() const
    {
      ASS_EQ(instrPrefix(), SUFFIX_INSTR);
      return static_cast<InstructionSuffix>(_info.suffix);
    }

    inline unsigned arg() const { return _info.arg; }
    inline CodeOp* alternative() const { return _alternative; }
    inline CodeOp*& alternative() { return _alternative; }

    inline void setAlternative(CodeOp* op) { ASS_NEQ(op, this); _alternative=op; }
    inline void setLongInstr(InstructionSuffix i) { _info.prefix=SUFFIX_INSTR; _info.suffix=i; }

    void makeFail() { _data=0; }

  private:
    inline size_t data() const { return _data; }

    inline void setArg(unsigned arg) { ASS_L(arg,1<<28); _info.arg=arg; }

    union {
      struct {
        unsigned prefix : 2;
        unsigned suffix : 2;
        unsigned arg : 28;
      } _info;
      void* _result;
      size_t _data;
    };
    /**
     * Pointer to an alternative operation
     *
     * If nonzero, either points to the first operation of
     * a @b CodeBlock or to a @b landingOp of a @b SearchStruct.
     */
    CodeOp* _alternative;
  };

  struct SearchStruct
  {
    void destroy();
    bool isFixedSearchStruct() const { return true; }

    bool getTargetOpPtr(const CodeOp& insertedOp, CodeOp**& tgt);

    CodeOp* getTargetOp(const FlatTerm::Entry* ftPos);

    enum Kind
    {
      FN_STRUCT,
      GROUND_TERM_STRUCT
    };

    CodeOp landingOp;
    Kind kind;
  protected:
    SearchStruct(Kind kind);
  };

  struct FixedSearchStruct
  : public SearchStruct
  {
    FixedSearchStruct(Kind kind, size_t length);
    ~FixedSearchStruct();

    size_t length;
    CodeOp** targets;
  };

  struct FnSearchStruct
  : public FixedSearchStruct
  {
    FnSearchStruct(size_t length);
    ~FnSearchStruct();
    CodeOp*& targetOp(unsigned fn);

    CLASS_NAME(CodeTree::FnSearchStruct);
    USE_ALLOCATOR(FnSearchStruct);

    struct OpComparator;

    unsigned* values;
  };

  struct GroundTermSearchStruct
  : public FixedSearchStruct
  {
    GroundTermSearchStruct(size_t length);
    ~GroundTermSearchStruct();
    CodeOp*& targetOp(const Term* trm);

    CLASS_NAME(CodeTree::GroundTermSearchStruct);
    USE_ALLOCATOR(GroundTermSearchStruct);

    struct OpComparator;

    Term** values;
  };


  typedef Vector<CodeOp> CodeBlock;
  typedef Stack<CodeOp> CodeStack;

  struct BaseMatcher
  {
  public:
    /**
     * Pointer to the current operation
     *
     * Must be initialized by inheritor (either directly or by
     * a call to the @b prepareLiteral function).
     */
    CodeOp* op;
  protected:

    bool doCheckGroundTerm();

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

  };

  //////// auxiliary methods //////////

  inline bool isEmpty() { return !_entryPoint; }
  inline CodeOp* getEntryPoint() { ASS(!isEmpty()); return &(*_entryPoint)[0]; }
  static CodeBlock* firstOpToCodeBlock(CodeOp* op);

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

  void compressCheckOps(CodeOp* chainStart, SearchStruct::Kind kind);

  static void compileTerm(Term* trm, CodeStack& code, CompileContext& cctx, bool addLitEnd);

  //////////// removal //////////////

  void optimizeMemoryAfterRemoval(Stack<CodeOp*>* firstsInBlocks, CodeOp* removedOp);

  struct RemovingMatcher
  : public BaseMatcher
  {
  public:
    bool next();

  protected:
    void init(CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_,
	CodeTree* tree_, Stack<CodeOp*>* firstsInBlocks_);


    bool prepareLiteral();
    bool backtrack();
    bool doSearchStruct();
    bool doCheckFun();
    bool doAssignVar();
    bool doCheckVar();


    struct BTPoint
    {
      BTPoint(size_t tp, CodeOp* op, size_t fibDepth)
      : tp(tp), op(op), fibDepth(fibDepth) {}

      size_t tp;
      CodeOp* op;
      size_t fibDepth;
    };

    /** Variable bindings */
    DArray<unsigned> bindings;

    Stack<BTPoint> btStack;
    Stack<CodeOp*>* firstsInBlocks;
    bool fresh;
    size_t curLInfo;

    CodeOp* entry;
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
    BTPoint(size_t tp, CodeOp* op) : tp(tp), op(op) {}

    /** Position in the flat term */
    size_t tp;
    /** Pointer to the next operation */
    CodeOp* op;
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
  : public BaseMatcher
  {
    void init(CodeTree* tree, CodeOp* entry_);

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
    /** Variable bindings */
    BindingArray bindings;

  protected:
    /** the matcher object is initialized but no execution of code was done yet */
    bool _fresh;
    bool _matched;

    /** Stack containing backtracking points */
    BTStack btStack;

    CodeOp* entry;

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

