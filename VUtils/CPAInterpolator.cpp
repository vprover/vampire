/**
 * @file CPAInterpolator.cpp
 * Implements class CPAInterpolator.
 */

#include <fstream>


#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"

#include "Parse/SMTLIB.hpp"

#include "CPAInterpolator.hpp"

namespace VUtils
{

using namespace Shell;

void CPAInterpolator::printUsageAndExit(int argc, char** argv)
{
  CALL("CPAInterpolator::printUsageAndExit");

  cout<< "Usage: " << endl
      << argv[0] <<" " << argv[1] <<" <file cnt> <left file cnt> <file...> <options>" <<endl;
  exit(0);
}

int CPAInterpolator::perform(int argc, char** argv)
{
  CALL("CPAInterpolator::perform");

  if(argc<5) {
    printUsageAndExit(argc, argv);
  }

  unsigned fileCnt;
  if(!Int::stringToUnsignedInt(argv[2], fileCnt) || fileCnt==0 || argc<4+fileCnt) {
    printUsageAndExit(argc, argv);
  }
  unsigned leftFileCnt;
  if(!Int::stringToUnsignedInt(argv[3], leftFileCnt) || leftFileCnt>fileCnt) {
    printUsageAndExit(argc, argv);
  }
  unsigned argIdx = 4;
  for(; argIdx<4+leftFileCnt; ++argIdx) {
    _leftFNames.push(argv[argIdx]);
  }
  for(; argIdx<4+fileCnt; ++argIdx) {
    _rightFNames.push(argv[argIdx]);
  }

  CommandLine cl(argc+1-argIdx,argv-1+argIdx);
  cl.interpret(*env.options);

  PROCESS_TRACE_SPEC_STRING(env.options->traceSpecString());
  env.options->enableTracesAccordingToOptions();

  if(_leftFNames.isNonEmpty() && _rightFNames.isNonEmpty()) {
    declareColors();
  }

}

void CPAInterpolator::collectSMTLIBFileFunctions(string fname, FuncSet& acc)
{
  CALL("CPAInterpolator::collectSMTLIBFileFunctions");

  ifstream stm(fname.c_str());

  Parse::SMTLIB pars(Parse::SMTLIB::DECLARE_SORTS);
  pars.parse(stm);
  typedef Stack<Parse::SMTLIB::FunctionInfo> FIStack;
  const Stack<Parse::SMTLIB::FunctionInfo>& fnInfs = pars.getFuncInfos();
  FIStack::ConstIterator fiit(fnInfs);
  while(fiit.hasNext()) {
    Parse::SMTLIB::FunctionInfo fi = fiit.next();
    FuncSpec spec(fi.name, fi.argSorts.size());
    acc.insert(spec);
    BaseType* type = pars.getSymbolType(fi);
    BaseType** pType;
    if(_funcTypes.getValuePtr(spec, pType)) {
      *pType = type;
    }
    else {
      if(**pType!=*type) {
	USER_ERROR("incompatible types for symbol "+fi.name);
      }
    }
  }
}

void CPAInterpolator::declareColors()
{
  CALL("CPAInterpolator::declareColors");

  FuncSet leftFuns;
  Stack<string>::Iterator lfIt(_leftFNames);
  while(lfIt.hasNext()) {
    collectSMTLIBFileFunctions(lfIt.next(), leftFuns);
  }

  FuncSet rightFuns;
  Stack<string>::Iterator lfIt(_rightFNames);
  while(lfIt.hasNext()) {
    collectSMTLIBFileFunctions(lfIt.next(), leftFuns);
  }

  FuncTypeMap::Iterator fit(_funcTypes);
  while(fit.hasNext()) {
    FuncSpec spec;
    BaseType* type;
    fit.next(spec, type);
    bool inLeft = leftFuns.contains(spec);
    bool inRight = rightFuns.contains(spec);
    ASS(inLeft || inRight);
    Color clr = inLeft ? (inRight ? COLOR_TRANSPARENT : COLOR_LEFT) : COLOR_RIGHT;

    bool isPred = !type->isFunctionType();

    string name = spec.first;
    unsigned arity = spec.second;
    unsigned symNum;
    Signature::Symbol* sym;
    bool added;
    if(isPred) {
      symNum = env.signature->addPredicate(name, arity, added);
      sym = env.signature->getPredicate(symNum);
    }
    else {
      symNum = env.signature->addFunction(name, arity, added);
      sym = env.signature->getFunction(symNum);
    }
    ASS(added);
    sym->setType(type);
    if(clr!=COLOR_TRANSPARENT) {
      sym->addColor(clr);
    }


  }
}

}
