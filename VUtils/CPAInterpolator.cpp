
/*
 * File CPAInterpolator.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file CPAInterpolator.cpp
 * Implements class CPAInterpolator.
 */

#include <fstream>
#include <cerrno>

#include <stdlib.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/wait.h>


#include "Lib/Environment.hpp"
#include "Lib/System.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "CASC/CASCMode.hpp"

#include "Shell/AIGInliner.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/InterpolantMinimizer.hpp"
#include "Shell/Interpolants.hpp"
#include "Shell/Options.hpp"
#include "Shell/ProofSimplifier.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/TPTPPrinter.hpp"

#include "Saturation/ProvingHelper.hpp"

#include "Parse/SMTLIB.hpp"

#include "CPAInterpolator.hpp"

namespace VUtils
{

using namespace Lib::Sys;
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
  env.options->setTimeLimitInSeconds(60);
  CommandLine cl(argc+1-argIdx,argv-1+argIdx);
  cl.interpret(*env.options);

  PROCESS_TRACE_SPEC_STRING(env.options->traceSpecString());
  env.options->enableTracesAccordingToOptions();

  if(_leftFNames.isNonEmpty() && _rightFNames.isNonEmpty()) {
    declareColors();
  }

  loadFormulas();

  doProving();

  return 0;
}

void CPAInterpolator::collectSMTLIBFileFunctions(vstring fname, FuncSet& acc)
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
  Stack<vstring>::Iterator lfIt(_leftFNames);
  while(lfIt.hasNext()) {
    collectSMTLIBFileFunctions(lfIt.next(), leftFuns);
  }

  FuncSet rightFuns;
  Stack<vstring>::Iterator rfIt(_rightFNames);
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

    vstring name = spec.first;
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

  Stack<vstring>::Iterator lfIt(_leftFNames);
  while(lfIt.hasNext()) {
    loadFormula(lfIt.next());
  }

  Stack<vstring>::Iterator rfIt(_rightFNames);
  while(rfIt.hasNext()) {
    loadFormula(rfIt.next());
  }

}

void CPAInterpolator::loadFormula(vstring fname)
{
  CALL("CPAInterpolator::loadFormula");

  ifstream stm(fname.c_str());

  Parse::SMTLIB pars(*env.options);
  pars.parse(stm);
  _forms = UnitList::concat(pars.getFormulas(), _forms);
  _defs = UnitList::concat(pars.getDefinitions(), _defs);

  _prb.addUnits(UnitList::copy(_forms));
}

void CPAInterpolator::doProving()
{
  CALL("CPAInterpolator::doProving");

  UIHelper::portfolioParent=true;
  env.timer->makeChildrenIncluded();

  Schedule quick;
  Schedule fallback;

  CASC::CASCMode::getSchedules(*_prb.getProperty(), quick, fallback);

  StrategySet usedStrategies;

  if(runSchedule(quick, usedStrategies, false)) {
    return;
  }
  if(!runSchedule(fallback, usedStrategies, true)) {
    if(fallback.isEmpty()) {
      env.beginOutput();
      env.out()<<"Ran out of schedules"<<endl;
      env.endOutput();
    }
  }
}

void CPAInterpolator::displayResult()
{
  CALL("CPAInterpolator::displayResult");
  AIGInliner::PremSet* dummy; //we don't care about premises here

  env.options->set("show_interpolant","off");

  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    Unit* refutation = env.statistics->refutation;

    ProofSimplifier simpl(_prb, UnitSpec(refutation), _defs);
    simpl.perform();
    UnitSpec newRef = simpl.getNewRefutation();
    ASS(newRef.withoutProp());
    refutation = newRef.unit();

    env.statistics->refutation = refutation;
  }


  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  if(env.statistics->terminationReason!=Statistics::REFUTATION) {
    return;
  }

  Unit* refutation = env.statistics->refutation;

  env.beginOutput();
  Formula* oldItp = Interpolants().getInterpolant(refutation);
  {
    AIGInliner inl;
    inl.addRelevant(oldItp);
    inl.scan(_defs);
    oldItp = Flattening::flatten(inl.apply(oldItp,dummy));
  }
  env.out() << "Old interpolant: " << TPTPPrinter::toString(oldItp) << endl;

  Formula* oldInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, true, true, "Original interpolant weight").getInterpolant(refutation);
  Formula* interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(refutation);
  InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, true, true, "Original interpolant count").getInterpolant(refutation);
  Formula* cntInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, false, true, "Minimized interpolant count").getInterpolant(refutation);
  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, true, true, "Original interpolant quantifiers").getInterpolant(refutation);
  Formula* quantInterpolant =  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, false, true, "Minimized interpolant quantifiers").getInterpolant(refutation);

  AIGInliner inl;
  inl.addRelevant(oldInterpolant);
  inl.addRelevant(interpolant);
  inl.addRelevant(cntInterpolant);
  inl.addRelevant(quantInterpolant);
  inl.scan(_defs);

//  oldInterpolant = inl.apply(oldInterpolant);
  interpolant = inl.apply(interpolant, dummy);
  cntInterpolant = inl.apply(cntInterpolant, dummy);
  quantInterpolant = inl.apply(quantInterpolant, dummy);

  env.out() << "Interpolant: " << TPTPPrinter::toString(interpolant) << endl;
  env.out() << "Count minimized interpolant: " << TPTPPrinter::toString(cntInterpolant) << endl;
  env.out() << "Quantifiers minimized interpolant: " << TPTPPrinter::toString(quantInterpolant) << endl;

  env.endOutput();
}

///////////////////////
// slicing
//

bool CPAInterpolator::tryMakeAdmissibleStrategy(Options& opt)
{
  CALL("CPAInterpolator::admissibleStrategy");
  /*
  if(opt.splitting()==Options::SM_BACKTRACKING) {
    return false;
    }*/
  if(opt.saturationAlgorithm()==Options::INST_GEN) {
    return false;
  }
  return true;
}

bool CPAInterpolator::runSchedule(Schedule& schedule,StrategySet& ss,bool fallback)
{
  CALL("CPAInterpolator::runSchedule");

  while (!schedule.isEmpty()) {
    vstring sliceCode = schedule.pop();
    vstring chopped;
    unsigned sliceTime = CASC::CASCMode::getSliceTime(sliceCode,chopped);
    if (fallback && ss.contains(chopped)) {
      continue;
    }
    ss.insert(chopped);
    int remainingTime = env.remainingTime()/100;
    if(remainingTime<=0) {
      return false;
    }
    // cast to unsigned is OK since realTimeRemaining is positive
    if(sliceTime > (unsigned)remainingTime) {
      sliceTime = remainingTime;
    }
    if(runSlice(sliceCode,sliceTime)) {
      return true;
    }
  }
  return false;
}

bool CPAInterpolator::runSlice(vstring slice, unsigned ds)
{
  CALL("CPAInterpolator::runSlice/2");

  Options opt=*env.options;
  opt.readFromTestId(slice);
  opt.setTimeLimitInDeciseconds(ds);
  int stl = opt.simulatedTimeLimit();
  if (stl) {
    opt.setSimulatedTimeLimit(int(stl * 1.1f));
  }

  if(!tryMakeAdmissibleStrategy(opt)) {
    return false;
  }

  env.beginOutput();
  env.out()<<"% slice "<<slice<<" for "<<ds<<" remaining "<<(env.remainingTime()/100)<<endl;
  env.endOutput();

  return runSlice(opt);
}


bool CPAInterpolator::runSlice(Options& opt)
{
  CALL("CPAInterpolator::runSlice/1");

  pid_t fres=Multiprocessing::instance()->fork();

  if(!fres) {
    childRun(opt);

    INVALID_OPERATION("ForkingCM::childRun should never return.");
  }

  System::ignoreSIGINT();

  int status;
  errno=0;
  pid_t res=waitpid(fres, &status, 0);
  if(res==-1) {
    SYSTEM_FAIL("Error in waiting for forked process.",errno);
  }

  System::heedSIGINT();

  Timer::syncClock();

  if(res!=fres) {
    INVALID_OPERATION("Invalid waitpid return value: "+Int::toString(res)+"  pid of forked Vampire: "+Int::toString(fres));
  }

  ASS(!WIFSTOPPED(status));

  if( (WIFSIGNALED(status) && WTERMSIG(status)==SIGINT) ||
      (WIFEXITED(status) && WEXITSTATUS(status)==3) )  {
    //if the forked Vampire was terminated by SIGINT (Ctrl+C), we also terminate
    //(3 is the return value for this case; see documentation for the
    //@b vampireReturnValue global variable)

    exit(VAMP_RESULT_STATUS_SIGINT);
  }

  if(WIFEXITED(status) && WEXITSTATUS(status)==0) {
    //if Vampire succeeds, its return value is zero
    return true;
  }

  return false;
}

/**
 * Do the theorem proving in a forked-off process
 */
void CPAInterpolator::childRun(Options& strategyOpt)
{
  CALL("CPAInterpolator::childRun");

  UIHelper::portfolioParent=false;
  int resultValue=1;
  env.timer->reset();
  env.timer->start();
  TimeCounter::reinitialize();

  Options opt(strategyOpt);

  //we have already performed the normalization
  opt.setNormalize(false);
  opt.setForcedOptionValues();
  opt.checkGlobalOptionConstraints();
  *env.options = opt; //just temporarily until we get rid of dependencies on env.options in solving
  env.options->setTimeLimitInDeciseconds(opt.timeLimitInDeciseconds());

  ProvingHelper::runVampire(_prb,opt);

  if(env.statistics->terminationReason==Statistics::REFUTATION) {
    displayResult();
    resultValue = 0;
  }
  exit(resultValue);
}





}
