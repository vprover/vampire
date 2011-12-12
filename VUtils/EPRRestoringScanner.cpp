/**
 * @file EPRRestoringScanner.cpp
 * Implements class EPRRestoringScanner.
 */

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/EqualityPropagator.hpp"
#include "Shell/EquivalenceDiscoverer.hpp"
#include "Shell/Options.hpp"
#include "Shell/PDInliner.hpp"
#include "Shell/PDMerger.hpp"
#include "Shell/PDUtils.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Property.hpp"
#include "Shell/UIHelper.hpp"

#include "EPRRestoringScanner.hpp"

namespace VUtils
{

using namespace Shell;

void EPRRestoringScanner::countClauses(Problem& prb, unsigned& allClauseCnt, unsigned& nonEprClauseCnt)
{
  CALL("EPRRestoringScanner::countClauses");

  allClauseCnt = 0;
  nonEprClauseCnt = 0;

  UnitList::Iterator uit(prb.units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    ASS(u->isClause()); //problem must be clausified
    allClauseCnt++;
    Clause* cl = static_cast<Clause*>(u);
    Clause::Iterator litIt(*cl);
    while(litIt.hasNext()) {
      Literal* lit = litIt.next();
      if(!lit->isShallow()) {
	nonEprClauseCnt++;
	goto next_clause;
      }
    }
  next_clause:;
  }
}

/**
 * We do just approximate check, i.e. don't eliminate circular definitions
 */
unsigned EPRRestoringScanner::countDefinitions(Problem& prb)
{
  CALL("EPRRestoringScanner::countDefinitions");

  unsigned res = 0;
  UnitList::Iterator uit(prb.units());
  while(uit.hasNext()) {
    Unit* u = uit.next();
    if(PDUtils::hasDefinitionShape(u)) {
      res++;
    }
  }
  return res;
}

void EPRRestoringScanner::computeEprResults(Problem& prb)
{
  CALL("EPRRestoringScanner::computeEprResults");

  _eprRes = UNDEF;

  int origArity = prb.getProperty()->maxFunArity();
  LOGV("vu_ers", origArity);
  if(origArity!=0) {
    _eprRes = FORM_NON_EPR;
  }
  Problem prbCl;
  prb.copyInto(prbCl, false);

  Preprocess prepro(_opts);
  prepro.preprocess(prbCl);

  countClauses(prbCl, _baseClauseCnt, _baseNonEPRClauseCnt);
  LOG("vu_ers", "Ordinary preprocessing finished, clause count: " << _baseClauseCnt <<" non-epr: " << _baseNonEPRClauseCnt);

  {
    EquivalenceDiscoverer ed(_useVariableNormalizationForSatEqDiscovery, _useUnitPropagationForSatEqDiscovery);
    _satDiscovered0 = ed.getEquivalences(prbCl.clauseIterator())->length();
    LOG("vu_ers", "Sat solver discoveder: " << _satDiscovered0 <<" equivlences in the unprocessed problem");
  }


  int clArity = prbCl.getProperty()->maxFunArity();
  LOGV("vu_ers", clArity);
  if(clArity==0 && _eprRes==UNDEF) {
    _eprRes = EASY_EPR;
  }

  Problem prbClRest;
  prb.copyInto(prbClRest, false);

  Options optsER = _opts;

  optsER.setEprPreservingNaming(true);
  optsER.setEprPreservingSkolemization(true);
  optsER.setEprRestoringInlining(true);
//  optsER.setEqualityPropagation(true);
  Preprocess prepro2(optsER);
  prepro2.preprocess(prbClRest);

  countClauses(prbClRest, _erClauseCnt, _erNonEPRClauseCnt);
  LOG("vu_ers", "Restoring preprocessing finished, clause count: " << _erClauseCnt <<" non-epr: " << _erNonEPRClauseCnt);

  int restArity = prbClRest.getProperty()->maxFunArity();

  LOGV("vu_ers", restArity);
  if(_eprRes==UNDEF) {
    if(restArity==0) {
      _eprRes = MADE_EPR_WITH_RESTORING;
    }
    else {
      _eprRes = CANNOT_MAKE_EPR;
    }
  }
}

void EPRRestoringScanner::computeInliningResults(Problem& prb0)
{
  CALL("EPRRestoringScanner::computeInliningResults");

  Problem prb;
  prb0.copyInto(prb, false);

  Preprocess prepro1(_opts);
  prepro1.preprocess1(prb);
  EqualityPropagator().apply(prb);

  _predDefCnt = countDefinitions(prb);
  LOG("vu_ers", "Definition count:" << _predDefCnt);


  Problem prbNG;
  prb.copyInto(prbNG, false);
  PDInliner(false, false,true).apply(prbNG);
  _predDefsNonGrowing = _predDefCnt - countDefinitions(prbNG);
  LOG("vu_ers", "Non-growing pred-defs: " << _predDefsNonGrowing);

  Problem prbDM;
  prb.copyInto(prbDM, false);
  PDMerger().apply(prbDM);
  _predDefsMerged = _predDefCnt - countDefinitions(prbDM);
  LOG("vu_ers", "Merged pred-defs: " << _predDefsMerged);

  PDMerger().apply(prbNG);
  _predDefsAfterNGAndMerge = countDefinitions(prbNG);
  LOG("vu_ers", "Definition count after non-growing inlining and merging: " << _predDefsAfterNGAndMerge);

  Options optsDMNG = _opts;

//  optsDMNG.setEqualityPropagation(true);
  optsDMNG.setPredicateDefinitionInlining(Options::INL_NON_GROWING);
  optsDMNG.setPredicateDefinitionMerging(true);


  bool firstIteration = true;
  _satDiscoveredIterativelyAfterNGM = 0;
  _satDiscoveryIterationCnt = 0;
start:

  Problem prbCl;
  prb.copyInto(prbCl, false);

  Preprocess prepro2(optsDMNG);
  prepro2.preprocess(prbCl);

  if(firstIteration) {
    countClauses(prbCl, _ngmClauseCnt, _ngmNonEPRClauseCnt);
    LOG("vu_ers", "Non-growing inlining and merging clause count: " << _ngmClauseCnt <<" non-epr: " << _ngmNonEPRClauseCnt);
  }

  EquivalenceDiscoverer ed(_useVariableNormalizationForSatEqDiscovery, _useUnitPropagationForSatEqDiscovery);
  UnitList* equivs = ed.getEquivalences(prbCl.clauseIterator());
  unsigned currentlyDiscovered = equivs->length();
  if(firstIteration) {
    _satDiscoveredAfterNGM = currentlyDiscovered;
    LOG("vu_ers", "Sat solver discovered: " << _satDiscoveredAfterNGM <<" equivlences in problem after non-growing inlining and merging");
    firstIteration = false;
  }
  _satDiscoveredIterativelyAfterNGM += currentlyDiscovered;
  if(currentlyDiscovered!=0 && _satDiscoveryIterationCnt<10) {
    _satDiscoveryIterationCnt++;
    prb.addUnits(equivs);
    goto start;
  }
}

void EPRRestoringScanner::reportResults()
{
  CALL("EPRRestoringScanner::reportResultAndExit");
  cout << _opts.problemName() << "\t";
  switch(_eprRes) {
  case MADE_EPR_WITH_RESTORING:
    cout << "MER";
    break;
  case CANNOT_MAKE_EPR:
    cout << "CME";
    break;
  case EASY_EPR:
    cout << "EPR";
    break;
  case FORM_NON_EPR:
    cout << "NEP";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  cout << "\t" << _baseClauseCnt << "\t" << _baseNonEPRClauseCnt << "\t" << _erClauseCnt << "\t" << _erNonEPRClauseCnt
       << "\t" << _predDefCnt << "\t" << _predDefsNonGrowing << "\t" << _predDefsMerged << "\t" << _predDefsAfterNGAndMerge
       << "\t" << _ngmClauseCnt << "\t" << _ngmNonEPRClauseCnt << "\t" << _satDiscovered0 << "\t" << _satDiscoveredAfterNGM
       << "\t" << _satDiscoveredIterativelyAfterNGM << "\t" << _satDiscoveryIterationCnt << endl;
}

int EPRRestoringScanner::perform(int argc, char** argv)
{
  CALL("EPRRestoringScanner::perform");

  if(argc<3) {
    USER_ERROR("file name expected as second argument");
  }
  string fname = argv[2];

  _opts.setTheoryAxioms(false);
  _opts.setInputFile(fname);

  _useUnitPropagationForSatEqDiscovery = true;
  _useVariableNormalizationForSatEqDiscovery = true;

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(_opts));

  computeEprResults(*prb);
  computeInliningResults(*prb);

  reportResults();
  return 0;
}


}
