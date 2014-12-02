/**
 * @file IndexManager.cpp
 * Implements class IndexManager.
 */

#include "Lib/Exception.hpp"

#include "Kernel/Grounder.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/SaturationAlgorithmContext.hpp"

#include "ArithmeticIndex.hpp"
#include "CodeTreeInterfaces.hpp"
#include "GroundingIndex.hpp"
#include "LiteralIndex.hpp"
#include "LiteralSubstitutionTree.hpp"
#include "TermIndex.hpp"
#include "TermSubstitutionTree.hpp"

#include "IndexManager.hpp"

using namespace Lib;
using namespace Indexing;

/*IndexManager::IndexManager(SaturationAlgorithm* alg) : _alg(alg), _genLitIndex(0)
{
  CALL("IndexManager::IndexManager");

  if(alg) {
    attach(alg);
  }
}*/

/*IndexManager::~IndexManager()
{
  CALL("IndexManager::~IndexManager");

  if(_alg) {
    release(GENERATING_SUBST_TREE);
  }
}*/

/*void IndexManager::setSaturationAlgorithm(SaturationAlgorithm* alg)
{
  CALL("IndexManager::setSaturationAlgorithm");
  //ASS(!_alg);
  ASS(alg);

  _alg = alg;
  attach(alg);
}*/

/*void IndexManager::attach(SaturationAlgorithm* salg)
{
  CALL("IndexManager::attach");

  request(GENERATING_SUBST_TREE);
}*/

Index* IndexManager::request(IndexType t)
{
  CALL("IndexManager::request");

  Entry e;
  if(getEntry(t,e)){
    e.refCnt++;
  } else {
      e.index = create(t);
      e.refCnt=1;
      e.local = isLocalIndex(t);
  }
  putEntry(t,e);
  return e.index;
}

void IndexManager::release(IndexType t)
{
  CALL("IndexManager::release");

  Entry e;

  cout << "release " << t << endl;
  if(!getEntry(t,e)){
    ASSERTION_VIOLATION;
  }

  e.refCnt--;
  if(e.refCnt==0) {
    if(t==GENERATING_SUBST_TREE) {
      _genLitIndex=0;
    }
    delete e.index;
    removeFromStore(t,e);
  } else {
    putEntry(t,e); 
  }
}

bool IndexManager::contains(IndexType t)
{
  Entry e;
  return getEntry(t,e);
}

/**
 * If IndexManager contains index @b t, return pointer to it
 *
 * The pointer can become invalid after return from the code that
 * has requested it through this function.
 */
Index* IndexManager::get(IndexType t)
{
  Entry e;
  getEntry(t,e);
  // will be null if getEntry returns false
  return e.index;
}

/**
 * Provide index form the outside
 *
 * There must not be index of the same type from before.
 * The provided index is never deleted by the IndexManager.
 */
void IndexManager::provideIndex(IndexType t, Index* index)
{
  CALL("IndexManager::provideIndex");

  Entry e;

  ASS(!getEntry(t,e));

  e.index = index;
  e.refCnt = 1; //reference to 1, so that we never delete the provided index
  e.local= isLocalIndex(t);
  putEntry(t,e);
}

Index* IndexManager::create(IndexType t)
{
  CALL("IndexManager::create");

  Index* res;
  LiteralIndexingStructure* is;
  TermIndexingStructure* tis;

  SaturationAlgorithm* alg = static_cast<SaturationAlgorithm*>(MainLoopContext::currentContext ->getMainLoop());

  //cout << "creating index " << t << endl;

  bool isGenerating;
  switch(t) {
  case GENERATING_SUBST_TREE:
#if COMPIT_GENERATOR==2
    is=new CompitUnificationRecordingLiteralSubstitutionTree();
#else
    is=new LiteralSubstitutionTree();
#endif
    _genLitIndex=is;

    //cout << "#1 " << endl;

    res=new GeneratingLiteralIndex(is);
    isGenerating = true;

    //cout << "#2 " << endl;

    break;
  case SIMPLIFYING_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new SimplifyingLiteralIndex(is);
    isGenerating = false;
    break;

  case SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = false;
    break;
  case GENERATING_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new UnitClauseLiteralIndex(is);
    isGenerating = true;
    break;
  case GENERATING_NON_UNIT_CLAUSE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new NonUnitClauseLiteralIndex(is);
    isGenerating = true;
    break;

  case SUPERPOSITION_SUBTERM_SUBST_TREE:
#if COMPIT_GENERATOR==1
    tis=new CompitUnificationRecordingTermSubstitutionTree();
#else
    tis=new TermSubstitutionTree();
#endif
    res=new SuperpositionSubtermIndex(tis, alg->getOrdering());
    isGenerating = true;
    break;
  case SUPERPOSITION_LHS_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new SuperpositionLHSIndex(tis, alg->getOrdering(), alg->getOptions());
    isGenerating = true;
    break;

  case DEMODULATION_SUBTERM_SUBST_TREE:
    tis=new TermSubstitutionTree();
    res=new DemodulationSubtermIndex(tis);
    isGenerating = false;
    break;
  case DEMODULATION_LHS_SUBST_TREE:
//    tis=new TermSubstitutionTree();
    tis=new CodeTreeTIS();
    res=new DemodulationLHSIndex(tis, alg->getOrdering(), alg->getOptions());
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_CODE_TREE:
    res=new CodeTreeSubsumptionIndex();
    isGenerating = false;
    break;

  case FW_SUBSUMPTION_SUBST_TREE:
    is=new LiteralSubstitutionTree();
//    is=new CodeTreeLIS();
    res=new FwSubsSimplifyingLiteralIndex(is);
    isGenerating = false;
    break;

  case REWRITE_RULE_SUBST_TREE:
    is=new LiteralSubstitutionTree();
    res=new RewriteRuleIndex(is, alg->getOrdering());
    isGenerating = false;
    break;

  case GLOBAL_SUBSUMPTION_INDEX:
  {
    Grounder* gnd = new GlobalSubsumptionGrounder();
    res = new GroundingIndex(gnd, alg->getOptions());
    isGenerating = false;
    break;
  }

//  case ARITHMETIC_INDEX:
//    res=new ArithmeticIndex();
//    isGenerating = false;
//    break;

  default:
    INVALID_OPERATION("Unsupported IndexType.");
  }
  //ASS(_alg);
  if(isGenerating) {
	//cout << "#3 " << endl;

    res->attachContainer(alg->getGeneratingClauseContainer());

    //cout << "#4 " << endl;

  }
  else {
    res->attachContainer(alg->getSimplifyingClauseContainer());
  }
  return res;
}
