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
//#define LOG_OP(x) std::cout<<x<<std::endl
//#define LOG_OP(x) if(TimeCounter::isBeingMeasured(TC_FORWARD_SUBSUMPTION)) { std::cout<<x<<std::endl; }

namespace Indexing {

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
    void init(ILStruct* ils, unsigned liIndex, Lib::DArray<TermList>& bindingArray);

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
  struct alignas(8) ILStruct
  {
    ILStruct(const Literal* lit, unsigned varCnt, Lib::Stack<unsigned>& gvnStack);
    ~ILStruct();
    void putIntoSequence(ILStruct* previous_);

    bool equalsForOpMatching(const ILStruct& o) const;

    void ensureFreshness(unsigned globalTimestamp);

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

    void addMatch(unsigned liIndex, Lib::DArray<TermList>& bindingArray);
    void deleteMatch(unsigned matchIndex);
    MatchInfo*& getMatch(unsigned matchIndex);

    unsigned matchCnt;

    /** all possible lits were tried to match */
    bool visited;
    bool finished;
    bool noNonOppositeMatches;
  private:
    Lib::DArray<MatchInfo*> matches;
  };

  enum Instruction
  {
    //it means fail if data==0
    SUCCESS_OR_FAIL = 0,
    CHECK_GROUND_TERM = 1,
    LIT_END = 2,
    CHECK_FUN = 3,
    ASSIGN_VAR = 4,
    CHECK_VAR = 5,
    SEARCH_STRUCT = 6,
  };

  /** Structure containing a single instruction and its arguments */
  struct CodeOp
  {
    template<class T> static CodeOp getSuccess(T* ptr)
    {
      ASS(ptr); //data has to be a non-zero pointer
      CodeOp res;
      res.setAlternative(0);
      res._setData(ptr);
      ASS(res.isSuccess());
      return res;
    }
    static CodeOp getLitEnd(ILStruct* ils);
    static CodeOp getTermOp(Instruction i, unsigned num);
    static CodeOp getGroundTermCheck(const Term* trm);

    bool equalsForOpMatching(const CodeOp& o) const;

    /**
     * Return true iff CodeOp contains a success instruction
     *
     * A success instruction is either SUCCESS or SUCCESS2, because
     * on some architectures, pointers are only 4-byte aligned and
     * the instruction is stored in first three bits.
     */
    inline bool isSuccess() const { return _instruction()==SUCCESS_OR_FAIL && _data<void>(); }
    inline bool isFail() const { return !_data<void>(); }
    inline bool isLitEnd() const { return _instruction()==LIT_END; }
    inline bool isSearchStruct() const { return _instruction()==SEARCH_STRUCT; }
    inline bool isCheckFun() const { return _instruction()==CHECK_FUN; }
    inline bool isCheckGroundTerm() const { return _instruction()==CHECK_GROUND_TERM; }

    inline Term* getTargetTerm() const
    {
      ASS(isCheckGroundTerm());
      return _data<Term>();
    }

    template<class T> inline T* getSuccessResult() { ASS(isSuccess()); return _data<T>(); }

    inline ILStruct* getILS()
    {
      ASS(isLitEnd());
      return _data<ILStruct>();
    }
    inline const ILStruct* getILS() const
    {
      return _data<ILStruct>();
    }

    const SearchStruct* getSearchStruct() const;
    SearchStruct* getSearchStruct();

    inline CodeOp* alternative() const { return _alternative; }
    inline CodeOp*& alternative() { return _alternative; }

    inline void setAlternative(CodeOp* op) { ASS_NEQ(op, this); _alternative=op; }

    void makeFail() { _setData<void>(0); }

    friend std::ostream& operator<<(std::ostream& out, const CodeOp& op);

    static constexpr unsigned
      INSTRUCTION_BITS_START = 0,
      INSTRUCTION_BITS_END = INSTRUCTION_BITS_START + 3,
      ARG_BITS_START = INSTRUCTION_BITS_END,
      ARG_BITS_END = CHAR_BIT * sizeof(uint64_t),
      DATA_BITS_START = 0,
      DATA_BITS_END = CHAR_BIT * sizeof(void *);

    static_assert(sizeof(void *) <= sizeof(uint64_t), "must be able to fit a pointer into a 64-bit integer");
    static_assert(SEARCH_STRUCT < 8, "must be able to squash instructions into 3 bits");
    static_assert(alignof(Term) == 8);

    // getters and setters
    BITFIELD64_GET_AND_SET(unsigned, instruction, Instruction, INSTRUCTION)
    BITFIELD64_GET_AND_SET(unsigned, arg, Arg, ARG)
    template<class T> T* _data() const
    { return reinterpret_cast<T*>(Lib::BitUtils::getBits<DATA_BITS_START, DATA_BITS_END>(this->_content)); }
    template<class T> void _setData(T* data)
    { Lib::BitUtils::setBits<DATA_BITS_START, DATA_BITS_END>(this->_content, reinterpret_cast<uint64_t>(data)); }
    // end bitfield

  private:
    uint64_t _content;

    /**
     * Pointer to an alternative operation
     *
     * If nonzero, either points to the first operation of
     * a @b CodeBlock or to a @b landingOp of a @b SearchStruct.
     */
    CodeOp* _alternative;
  };

  /**
   * A search structure that collects alternatives of the same
   * kind (either function symbols or ground terms) and offers
   * more efficient searching and insertion over them.
   */
  struct SearchStruct
  {
    void destroy();
    /**
     * Fills out pointer @b tgt where @b insertedOp should be
     * (or is) inserted in the structure. If @b doInsert is true
     * an entry is inserted if not found.
     */
    template<bool doInsert>
    bool getTargetOpPtr(const CodeOp& insertedOp, CodeOp**& tgt);

    /**
     * Returns code op in the structure matching the content
     * of flat term entry @b ftPos.
     */
    CodeOp* getTargetOp(const FlatTerm::Entry* ftPos);
    inline size_t length() const { return targets.size(); }

    enum Kind
    {
      FN_STRUCT,
      GROUND_TERM_STRUCT
    };

    /**
     * Actual code op for this search structure. This construction
     * implies that search structure operations cannot be stored
     * in @b CodeBlock containers.
     */
    CodeOp landingOp;
    Kind kind;
    std::vector<CodeOp*> targets;

  protected:
    SearchStruct(Kind kind, size_t length);
  };

  template<SearchStruct::Kind k>
  struct SearchStructImpl
  : public SearchStruct
  {
    SearchStructImpl(size_t length);

    using T = typename std::conditional<k==SearchStruct::FN_STRUCT,unsigned,Term*>::type;

    /**
     * Tries to find the code op in @b targets at position where @b val is in @b values.
     * If exact code op is not found and @b doInsert is true, an entry is inserted
     * into @b values and @b targets. Otherwise, some code op is returned where
     * the entry should be (or is) stored as an alternative.
     */
    template<bool doInsert> CodeOp*& targetOp(const T& val);

    std::vector<T> values;
  };

  using FnSearchStruct = SearchStructImpl<SearchStruct::FN_STRUCT>;
  using GroundTermSearchStruct = SearchStructImpl<SearchStruct::GROUND_TERM_STRUCT>;

  typedef Lib::Vector<CodeOp> CodeBlock;
  typedef Lib::Stack<CodeOp> CodeStack;

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

  inline bool isEmpty() const { return !_entryPoint; }
  inline CodeOp* getEntryPoint() const { ASS(!isEmpty()); return &(*_entryPoint)[0]; }
  static CodeBlock* firstOpToCodeBlock(CodeOp* op);

  template<class Visitor>
  void visitAllOps(Visitor visitor) const;

  friend std::ostream& operator<<(std::ostream& out, const CodeTree& ct);

  //////////// insertion //////////////

  typedef Lib::DHMap<unsigned,unsigned> VarMap;

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

  template<SearchStruct::Kind k>
  void compressCheckOps(CodeOp* chainStart);

  static void compileTerm(const Term* trm, CodeStack& code, CompileContext& cctx, bool addLitEnd);

  //////////// removal //////////////

  void optimizeMemoryAfterRemoval(Lib::Stack<CodeOp*>* firstsInBlocks, CodeOp* removedOp);

  struct RemovingMatcher
  : public BaseMatcher
  {
  public:
    bool next();

    bool keepRecycled() const
    { return bindings.keepRecycled() 
        || btStack.keepRecycled() 
        || (firstsInBlocks && firstsInBlocks->keepRecycled()); }

  protected:
    void init(CodeOp* entry_, LitInfo* linfos_, size_t linfoCnt_,
	CodeTree* tree_, Lib::Stack<CodeOp*>* firstsInBlocks_);


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
    Lib::DArray<unsigned> bindings;

    Lib::Stack<BTPoint> btStack;
    Lib::Stack<CodeOp*>* firstsInBlocks;
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

  typedef Lib::Stack<BTPoint> BTStack;
  typedef Lib::DArray<TermList> BindingArray;

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
    bool keepRecycled() const { return bindings.keepRecycled(); }

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

