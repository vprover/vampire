
/*
 * File vutil.cpp.
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
 * @file vutil.cpp. Implements the main function for running small tools thet use Vampire's infrastructure.
 */

#include <iostream>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"
#include "Lib/VString.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "CASC/CASCMode.hpp"

#include "VUtils/AnnotationColoring.hpp"
#include "VUtils/CPAInterpolator.hpp"
#include "VUtils/DPTester.hpp"
#include "VUtils/EPRRestoringScanner.hpp"
#include "VUtils/FOEquivalenceDiscovery.hpp"
#include "VUtils/PreprocessingEvaluator.hpp"
#include "VUtils/ProblemColoring.hpp"
#include "VUtils/SATReplayer.hpp"
#include "VUtils/SimpleSMT.hpp"
#include "VUtils/SMTLIBConcat.hpp"
#include "VUtils/Z3InterpolantExtractor.hpp"

using namespace Lib;
using namespace Shell;
using namespace CASC;
using namespace VUtils;


void explainException (Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

void readAndFilterGlobalOpts(Stack<char*>& args) {
  Stack<char*>::StableDelIterator it(args);

  //skip the first item which is the executable name
  ALWAYS(it.hasNext());
  it.next();

  while(it.hasNext()) {
    vstring arg(it.next());
    if(arg=="-tr") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -tr option expected");
      }
      vstring traceStr(it.next());
      it.del();
      PROCESS_TRACE_SPEC_STRING(traceStr);
    }
    else if(arg=="-m") {
      it.del();
      if(!it.hasNext()) {
	USER_ERROR("value for -m option expected");
      }
      vstring memLimitStr = it.next();
      it.del();
      unsigned memLimit;
      if(!Int::stringToUnsignedInt(memLimitStr, memLimit)) {
	USER_ERROR("unsigned number expected as value of -m option");
      }
      env.options->setMemoryLimit(memLimit);
      Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    }
    else {
      break;
    }
  }
}

/**
 * The main function.
  */
int main(int argc, char* argv [])
{
  CALL ("main");

  int resultValue=2;

  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
   // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  Stack<char*> args;
  args.loadFromIterator(getArrayishObjectIterator(argv, argc));

  try {
    env.options->setMode(Options::MODE_VAMPIRE);
    env.options->setTimeLimitInDeciseconds(0);

    Allocator::setMemoryLimit(1024u*1048576ul);

    readAndFilterGlobalOpts(args);

    if(args.size()<2) {
      USER_ERROR("missing name of the vutil module to be run (vutil requires at least one command line argument)");
    }
    vstring module=args[1];
    if(module=="problem_coloring") {
      resultValue=ProblemColoring().perform(args.size(), args.begin());
    }
    else if(module=="conjecture_coloring" || module=="axiom_coloring") {
      resultValue=AnnotationColoring().perform(args.size(), args.begin());
    }
    else if(module=="zie") {
      resultValue=ZIE().perform(args.size(), args.begin());
    }
    else if(module=="epr_restoring_scanner") {
      resultValue=EPRRestoringScanner().perform(args.size(), args.begin());
    }
    else if(module=="fed") {
      resultValue=FOEquivalenceDiscovery().perform(args.size(), args.begin());
    }
    else if(module=="sc") {
      resultValue=SMTLIBConcat().perform(args.size(), args.begin());
    }
    else if(module=="cpa") {
      resultValue=CPAInterpolator().perform(args.size(), args.begin());
    }
    else if(module=="pe") {
      resultValue=PreprocessingEvaluator().perform(args.size(), args.begin());
    }
    else if(module=="smt") {
      resultValue=SimpleSMT().perform(args.size(), args.begin());
      
    }
    else if(module=="dpt") {
      resultValue=DPTester().perform(args.size(), args.begin());
    }
    else if(module=="sr") {
      resultValue=SATReplayer().perform(args.size(), args.begin());
    }
    else if(module=="vamp_casc") {
      Shell::CommandLine cl(args.size()-1, args.begin()+1);
      cl.interpret(*env.options);
      Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
      Lib::Random::setSeed(env.options->randomSeed());
      if(CASC::CASCMode::perform(args.size()-1, args.begin()+1)) {
	//casc mode succeeded in solving the problem, so we return zero
	resultValue = VAMP_RESULT_STATUS_SUCCESS;
      }
    }
    else {
      USER_ERROR("unknown vutil module name: "+module);
    }
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
    reportSpiderFail();
  }
#endif
  catch (UserErrorException& exception) {
    reportSpiderFail();
    explainException(exception);
  }
  catch (Exception& exception) {
    reportSpiderFail();
    env.beginOutput();
    explainException(exception);
    env.statistics->print(env.out());
    env.endOutput();
  }
  catch (std::bad_alloc& _) {
    reportSpiderFail();
    env.beginOutput();
    env.out() << "Insufficient system memory" << '\n';
    env.endOutput();
  }
//   delete env.allocator;

  return resultValue;
} // main

