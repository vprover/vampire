/**
 * @file CPAInterpolator.cpp
 * Implements class CPAInterpolator.
 */

#include <fstream>


#include "Lib/Environment.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Shell/AIGInliner.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/InterpolantMinimizer.hpp"
#include "Shell/Interpolants.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/TPTP.hpp"

#include "Saturation/ProvingHelper.hpp"

#include "Parse/SMTLIB.hpp"

#include "CPAInterpolator.hpp"

namespace VUtils
{

using namespace Saturation;
using namespace Shell;

void CPAInterpolator::printUsageAndExit(unsigned argc, char** argv)
{
  CALL("CPAInterpolator::printUsageAndExit");

  cout<< "Usage: " << endl
      << argv[0] <<" " << argv[1] <<" <file cnt> <left file cnt> <file...> <options>" <<endl;
  exit(0);
}

int CPAInterpolator::perform(unsigned argc, char** argv)
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

  env.options->set("smtlib_consider_ints_real", "on");
  CommandLine cl(argc+1-argIdx,argv-1+argIdx);
  cl.interpret(*env.options);

  PROCESS_TRACE_SPEC_STRING(env.options->traceSpecString());
  env.options->enableTracesAccordingToOptions();

  if(_leftFNames.isNonEmpty() && _rightFNames.isNonEmpty()) {
    declareColors();
  }

  loadFormulas();

  doProving();

  displayResult();

  return 0;
}

void CPAInterpolator::collectSMTLIBFileFunctions(string fname, FuncSet& acc)
{
  CALL("CPAInterpolator::collectSMTLIBFileFunctions");

  ifstream stm(fname.c_str());

  Parse::SMTLIB pars(*env.options, Parse::SMTLIB::DECLARE_SORTS);
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

  env.colorUsed = true;

  FuncSet leftFuns;
  Stack<string>::Iterator lfIt(_leftFNames);
  while(lfIt.hasNext()) {
    collectSMTLIBFileFunctions(lfIt.next(), leftFuns);
  }

  FuncSet rightFuns;
  Stack<string>::Iterator rfIt(_rightFNames);
  while(rfIt.hasNext()) {
    collectSMTLIBFileFunctions(rfIt.next(), rightFuns);
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

void CPAInterpolator::loadFormulas()
{
  CALL("CPAInterpolator::loadFormulas");

  _forms = 0;
  _defs = 0;

  Stack<string>::Iterator lfIt(_leftFNames);
  while(lfIt.hasNext()) {
    loadFormula(lfIt.next());
  }

  Stack<string>::Iterator rfIt(_rightFNames);
  while(rfIt.hasNext()) {
    loadFormula(rfIt.next());
  }

}

void CPAInterpolator::loadFormula(string fname)
{
  CALL("CPAInterpolator::loadFormula");

  ifstream stm(fname.c_str());

  Parse::SMTLIB pars(*env.options);
  pars.parse(stm);
  _forms = UnitList::concat(pars.getFormulas(), _forms);
  _defs = UnitList::concat(pars.getDefinitions(), _defs);
}

void CPAInterpolator::doProving()
{
  CALL("CPAInterpolator::doProving");

  Problem prb;
  prb.addUnits(_forms->copy());

  ProvingHelper::runVampire(prb, *env.options);
}

void CPAInterpolator::displayResult()
{
  CALL("CPAInterpolator::displayResult");

  env.options->set("show_interpolant","off");

  env.beginOutput();
  UIHelper::outputResult(env.out());

  Formula* oldItp = Interpolants().getInterpolant(env.statistics->refutation);
  {
    AIGInliner inl;
    inl.addRelevant(oldItp);
    inl.scan(_defs);
    oldItp = inl.apply(oldItp);
  }
  env.out() << "Old interpolant: " << TPTP::toString(oldItp) << endl;


  Formula* oldInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, true, true, "Original interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
  Formula* interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
  InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, true, true, "Original interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
  Formula* cntInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, false, true, "Minimized interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
  Formula* quantInterpolant =  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, false, true, "Minimized interpolant quantifiers").getInterpolant(static_cast<Clause*>(env.statistics->refutation));

  AIGInliner inl;
  inl.addRelevant(oldInterpolant);
  inl.addRelevant(interpolant);
  inl.addRelevant(cntInterpolant);
  inl.addRelevant(quantInterpolant);
  inl.scan(_defs);

  oldInterpolant = inl.apply(oldInterpolant);
  interpolant = inl.apply(interpolant);
  cntInterpolant = inl.apply(cntInterpolant);
  quantInterpolant = inl.apply(quantInterpolant);

  env.out() << "Interpolant: " << TPTP::toString(interpolant) << endl;
  env.out() << "Count minimized interpolant: " << TPTP::toString(cntInterpolant) << endl;
  env.out() << "Quantifiers minimized interpolant: " << TPTP::toString(quantInterpolant) << endl;

  env.endOutput();
}

}
