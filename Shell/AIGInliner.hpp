/**
 * @file AIGInliner.hpp
 * Defines class AIGInliner.
 */

#ifndef __AIGInliner__
#define __AIGInliner__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/MapToLIFO.hpp"

#include "AIG.hpp"
#include "AIGCompressor.hpp"

namespace Shell {

using namespace Indexing;


class AIGInliner : public ScanAndApplyFormulaUnitTransformer {

  struct EquivInfo {
    EquivInfo(Literal* lhs, Formula* rhs, FormulaUnit* unit);

    //these are initialized by constructor
    Literal* lhs;
    Formula* rhs;
    FormulaUnit* unit;
    Literal* posLhs;
    bool active;

    //these are initialized in AIGInliner::addInfo()
    AIGRef activeAIGRhs;

//    //unused
//
//    AIGRef activeAIGLhs;
//
//    AIGRef initAIGLhs;
//    AIGRef initAIGRhs;
//
//    AIGRef outputAIGLhs;
//    AIGRef outputAIGRhs;
//    FormulaUnit* outputUnit;


    CLASS_NAME("AIGInliner::EquivInfo");
    USE_ALLOCATOR(EquivInfo);

    static bool litIsLess(Literal* l1, Literal* l2);
    static EquivInfo* tryGetEquiv(FormulaUnit* fu);
  };

  //options
  bool _onlySingleAtomPreds;

  Stack<EquivInfo*> _eqInfos;

  LiteralSubstitutionTree* _lhsIdx;
  DHMap<Literal*, EquivInfo*> _defs;
  DHMap<FormulaUnit*, EquivInfo*> _unit2def;

  DHMap<AIGRef,AIGRef> _inlMap;
  DHMap<AIGRef,AIGRef> _simplMap;

#if VDEBUG
  //to check whether we collect all relevant AIGs
  DHSet<AIGRef> _relevantAigs;
#endif

  AIGFormulaSharer _fsh;
  AIG& _aig;
  AIGTransformer _atr;
  AIGCompressor _acompr;

  bool addInfo(EquivInfo* inf);
  void collectDefinitions(UnitList* units, Stack<AIGRef>& relevantAigs);
  bool tryExpandAtom(AIGRef atom, AIGRef& res);

  AIGRef apply(AIGRef a);
  Formula* apply(Formula* a);

public:
  AIGInliner();
  ~AIGInliner();

  using ScanAndApplyFormulaUnitTransformer::apply;

  void scan(UnitList* units);
  virtual bool apply(FormulaUnit* unit, Unit*& res);

protected:
  virtual void updateModifiedProblem(Problem& prb);
};


class AIGDefinitionIntroducer : public ScanAndApplyFormulaUnitTransformer
{
  typedef SharedSet<unsigned> VarSet;

  struct NodeInfo {

    //these members are filled-in in the doFirstRefAIGPass() function

    /** True if contains quantifiers with {negative,positive} polarity */
    bool _hasQuant[2];
    bool _hasName;
    AIGRef _name;
    VarSet* _freeVars;

    /** Number of AIG nodes that refer to this node */
    unsigned _directRefCnt;

    //these members are filled-in in the doSecondRefAIGPass() function

    /** True if occurs in toplevel AIGs with {negative,positive} polarity */
    bool _inPol[2];
    /** True if occurs in quantifier AIG nodes with {negative,positive} polarity */
    bool _inQuant[2];

    /**
     * How many times will an AIG node appear in formulas
     * after conversion of AIG to formulas
     *
     * Equals to 1 if node has a name
     */
    unsigned _formRefCnt;
  };

  struct DefIntroRewriter;

  //options
  bool _eprPreserving;
  unsigned _namingRefCntThreshold;
  unsigned _mergeEquivDefs;

  AIGFormulaSharer _fsh;

  typedef Stack<AIGRef> TopLevelStack;
  TopLevelStack _toplevelAIGs;

  /**
   * All positive AIG refs used in the problem, ordered topologically,
   * so that references go only toward the bottom of the stack.
   */
  AIGStack _refAIGs;
  /** stack of infos corresponding to nodes at corresponding _refAIGs positions */
  Stack<NodeInfo> _refAIGInfos;
  /** Indexes of AIG refs in the _refAIGs stack */
  DHMap<AIGRef,size_t> _aigIndexes;

  DHMap<AIGRef,AIGRef> _defs;
  DHMap<AIGRef,FormulaUnit*> _defUnits;

//  DHMap<Literal*,Literal*> _equivs;

  Stack<FormulaUnit*> _newDefs;

  AIGRef getPreNamingAig(unsigned aigStackIdx);

  bool shouldIntroduceName(unsigned aigStackIdx);
  Literal* getNameLiteral(unsigned aigStackIdx);
  void introduceName(unsigned aigStackIdx);

  bool scanDefinition(FormulaUnit* def);

  //functions called from scan()
  void collectTopLevelAIGsAndDefs(UnitList* units);
  void processTopLevelAIGs();

  //functions called from processTopLevelAIGs()
  void doFirstRefAIGPass();
  void doSecondRefAIGPass();

  VarSet* getAtomVars(Literal* l);
  NodeInfo& getNodeInfo(AIGRef r);

public:
  AIGDefinitionIntroducer(unsigned threshold=4);

  virtual void scan(UnitList* units);

  using ScanAndApplyFormulaUnitTransformer::apply;
  virtual bool apply(FormulaUnit* unit, Unit*& res);

  virtual UnitList* getIntroducedFormulas();

  Formula* apply(Formula* f, UnitList*& introducedDefs);
protected:
  virtual void updateModifiedProblem(Problem& prb) {}
};



}

#endif // __AIGInliner__
