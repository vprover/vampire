/**
 * @file EPRRestoringScanner.cpp
 * Implements class EPRRestoringScanner.
 */

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "Shell/UIHelper.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"

#include "EPRRestoringScanner.hpp"

namespace VUtils
{

using namespace Shell;

void EPRRestoringScanner::countClauses(Problem& prb, unsigned& allClauseCnt, unsigned& nonEprClauseCnt)
{
  CALL("EPRRestoringScanner::countClauses");
  NOT_IMPLEMENTED;
}

void EPRRestoringScanner::computeEprResults()
{
  CALL("EPRRestoringScanner::computeEprResults");

  _eprRes = UNDEF;

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(_opts));
  int origArity = prb->getProperty()->maxFunArity();
  LOGV("vu_ers", origArity);
  if(origArity!=0) {
    _eprRes = FORM_NON_EPR;
  }
  Problem prbCl;
  prb->copyInto(prbCl, false);

  Preprocess prepro(_opts);
  prepro.preprocess(prbCl);

  countClauses(prbCl, _baseClauseCnt, _baseNonEPRClauseCnt);

  int clArity = prbCl.getProperty()->maxFunArity();
  LOGV("vu_ers", clArity);
  if(clArity==0 && _eprRes==UNDEF) {
    _eprRes = FORM_NON_EPR;
  }

  Problem prbClRest;
  prb->copyInto(prbClRest, false);

  _opts.setEprPreservingNaming(true);
  _opts.setEprPreservingSkolemization(true);
  _opts.setEprRestoringInlining(true);
  Preprocess prepro2(_opts);
  prepro2.preprocess(prbClRest);

  countClauses(prbCl, _erClauseCnt, _erNonEPRClauseCnt);

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

void EPRRestoringScanner::reportResult(EprResult res)
{
  CALL("EPRRestoringScanner::reportResultAndExit");
  cout << _opts.problemName() << ": ";
  switch(res) {
  case MADE_EPR_WITH_RESTORING:
    cout << "made epr with restoring" << endl;
    break;
  case CANNOT_MAKE_EPR:
    cout << "cannot make EPR" << endl;
    break;
  case EASY_EPR:
    cout << "restoring not needed to make EPR" << endl;
    break;
  case FORM_NON_EPR:
    cout << "not EPR" << endl;
    break;
  }
  exit(res);
}

int EPRRestoringScanner::perform(int argc, char** argv)
{
  CALL("EPRRestoringScanner::perform");

  if(argc<3) {
    USER_ERROR("file name expected as second argument");
  }
  string fname = argv[2];

  _opts.setInputFile(fname);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(_opts));
  int origArity = prb->getProperty()->maxFunArity();
  LOGV("vu_ers", origArity);
  if(origArity!=0) {
    reportResultAndExit(FORM_NON_EPR);
  }
  Problem prbCl;
  prb->copyInto(prbCl, false);

  Preprocess prepro(_opts);
  prepro.preprocess(prbCl);

  int clArity = prbCl.getProperty()->maxFunArity();
  LOGV("vu_ers", clArity);
  if(clArity==0) {
    reportResultAndExit(EASY_EPR);
  }

  Problem prbClRest;
  prb->copyInto(prbClRest, false);

  _opts.setEprPreservingNaming(true);
  _opts.setEprPreservingSkolemization(true);
  _opts.setEprRestoringInlining(true);
  Preprocess prepro2(_opts);
  prepro2.preprocess(prbClRest);

  int restArity = prbClRest.getProperty()->maxFunArity();
  LOGV("vu_ers", restArity);
  if(restArity==0) {
    reportResultAndExit(MADE_EPR_WITH_RESTORING);
  }
  else {
    reportResultAndExit(CANNOT_MAKE_EPR);
  }
  ASSERTION_VIOLATION;
}


}
