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
#include "AIGRewriter.hpp"

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


    CLASS_NAME(AIGInliner::EquivInfo);
    USE_ALLOCATOR(EquivInfo);

    static bool litIsLess(Literal* l1, Literal* l2);
    static EquivInfo* tryGetEquiv(FormulaUnit* fu);
  };

  //options
  bool _onlySingleAtomPreds;

  Stack<AIGRef> _relevantAigs;

  Stack<EquivInfo*> _eqInfos;

  LiteralSubstitutionTree* _lhsIdx;
  DHMap<Literal*, EquivInfo*> _defs;
  DHMap<FormulaUnit*, EquivInfo*> _unit2def;

public:
  typedef AIGRewriter::PremiseSet PremSet;
  typedef AIGRewriter::PremRef PremRef;
  typedef AIGRewriter::RefMap PremRefMap;
  typedef DHMap<AIGRef,AIGRef> RefMap;
private:
  PremRefMap _inlMap;
  RefMap _simplMap;

#if VDEBUG
  //to check whether we collect all relevant AIGs
  DHSet<AIGRef> _relevantAigsSet;
#endif

  mutable AIGFormulaSharer _fsh;
  AIG& _aig;
  AIGRewriter _atr;
  AIGCompressor _acompr;



  bool addInfo(EquivInfo* inf);
  void collectDefinitionsAndRelevant(UnitList* units);
  bool tryExpandAtom(AIGRef atom, PremRef& res);


public:
  AIGInliner();
  ~AIGInliner();

  AIG& aig() const { return _aig; }
  AIGFormulaSharer& fsh() const { return _fsh; }

  using ScanAndApplyFormulaUnitTransformer::apply;

  void scan(UnitList* units);
  virtual bool apply(FormulaUnit* unit, Unit*& res);

  void addRelevant(AIGRef a);
  void addRelevant(Formula* f);
  AIGRef apply(AIGRef a, PremSet*& prems);
  Formula* apply(Formula* f, PremSet*& prems);

protected:
  virtual void updateModifiedProblem(Problem& prb);
};



}

#endif // __AIGInliner__
