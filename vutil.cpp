/**
 * @file vutil.cpp. Implements the main function for running small tools thet use Vampire's infrastructure.
 */

#include <string>
#include <iostream>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Random.hpp"
#include "Lib/System.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "VUtils/AnnotationColoring.hpp"
#include "VUtils/ProblemColoring.hpp"

using namespace Lib;
using namespace Shell;
using namespace VUtils;


void explainException (Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

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

  try {
    env.options->setMode(Options::MODE_VAMPIRE);
    env.options->setTimeLimitInDeciseconds(0);

    Allocator::setMemoryLimit(1024u*1048576ul);

    if(argc<2) {
      USER_ERROR("missing name of the vutil module to be run (vutil requires at least one command line argument)");
    }
    string module=argv[1];
    if(module=="problem_coloring") {
      resultValue=ProblemColoring().perform(argc, argv);
    }
    else if(module=="conjecture_coloring" || module=="axiom_coloring") {
      resultValue=AnnotationColoring().perform(argc, argv);
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

