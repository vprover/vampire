/**
 * @file AIGInliner.hpp
 * Defines class AIGInliner.
 */

#ifndef __AIGInliner__
#define __AIGInliner__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/MapToLIFO.hpp"

#include "AIG.hpp"

namespace Shell {

class AIGInliner : public ScanAndApplyFormulaUnitTransformer {

  //options
  bool _onlySingleAtomPreds;

  AIGFormulaSharer _fsh;
  DHMap<FormulaUnit*,FormulaUnit*> _defReplacements;

  MapToLIFO<unsigned,Literal*> _predLits;
  DHSet<unsigned> _clPreds;

  //functions called from scan(UnitList*)
  void scanOccurrences(UnitList* units);
  void collectDefinitions(UnitList* units, FormulaStack& lhsForms, FormulaStack& rhsForms, Stack<FormulaUnit*>& defUnits);
  void addDefinitionReplacement(Formula* lhs, Formula* rhs, FormulaUnit* unit);


public:
  AIGInliner();

  using ScanAndApplyFormulaUnitTransformer::apply;

  void scan(UnitList* units);
  bool apply(FormulaUnit* unit, FormulaUnit*& res);

protected:
  virtual void updateModifiedProblem(Problem& prb);
};

class AIGDefinitionIntroducer : public ScanAndApplyFormulaUnitTransformer
{

  struct NodeInfo {

    //these members are filled-in in the doFirstRefAIGPass() function

    /** True if contains quantifiers with {negative,positive} polarity */
    bool _hasQuant[2];
    Literal* _name;
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

  AIGStack _toplevelAIGs;

  /**
   * All positive AIG refs used in the problem, ordered topologically,
   * so that references go only toward the bottom of the stack.
   */
  AIGStack _refAIGs;
  /** stack of infos corresponding to nodes at corresponding _refAIGs positions */
  Stack<NodeInfo> _refAIGInfos;
  /** Indexes of AIG refs in the _refAIGs stack */
  DHMap<AIGRef,size_t> _aigIndexes;

  DHMap<AIGRef,Literal*> _defs;
  DHMap<AIGRef,FormulaUnit*> _defUnits;

  DHMap<Literal*,Literal*> _equivs;

  Stack<FormulaUnit*> _newDefs;


  bool shouldIntroduceName(unsigned aigStackIdx);
  Literal* getNameLiteral(unsigned aigStackIdx);
  void introduceName(unsigned aigStackIdx);

  void scanDefinition(FormulaUnit* def);

  //functions called from scan()
  void collectTopLevelAIGsAndDefs(UnitList* units);
  void doFirstRefAIGPass();
  void doSecondRefAIGPass();

public:
  AIGDefinitionIntroducer(const Options& opts);

  void scan(UnitList* units);

  using ScanAndApplyFormulaUnitTransformer::apply;
  bool apply(FormulaUnit* unit, FormulaUnit*& res);

  virtual UnitList* getIntroducedFormulas();
protected:
  virtual void updateModifiedProblem(Problem& prb) {}
};



}

#endif // __AIGInliner__
