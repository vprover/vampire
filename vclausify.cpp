
/*
 * File vclausify.cpp.
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
 * @file vclausify.cpp. Implements the main function for a separate executable that only performs clausification.
 */

#include <iostream>

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"
#include "Lib/VString.hpp"
#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTP.hpp"
#include "Shell/UIHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;

UnitList* globUnitList=0;
Problem* globProblem=0;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interrupted by a SIGINT, value 3 is returned,
 * and in case of other signal we return 2. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case Vampire was terminated by the timer, return value is
 * uncertain (but definitely not zero), probably it will be 134
 * (we terminate by a call to the @b abort() function in this case).
 */
int vampireReturnValue = 1;

Problem* getPreprocessedProblem()
{
  CALL("getInputClauses");

  Problem* prb=UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);
  globProblem=prb;

  return prb;
}

void clausifyMode()
{
  CALL("clausifyMode()");

  CompositeISE simplifier;
  simplifier.addFront(new TrivialInequalitiesRemovalISE());
  simplifier.addFront(new TautologyDeletionISE());
  simplifier.addFront(new DuplicateLiteralRemovalISE());

  ScopedPtr<Problem> prb(getPreprocessedProblem());

  env.beginOutput();
  UIHelper::outputSymbolDeclarations(env.out());

  ClauseIterator cit = prb->clauseIterator();
  while (cit.hasNext()) {
    Clause* cl=cit.next();
    cl=simplifier.simplify(cl);
    if(!cl) {
      continue;
    }
    env.out() << TPTP::toString(cl) << "\n";
  }
  env.endOutput();

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // clausifyMode


void explainException (Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

/**
 * The main function.
  * @since 03/12/2003 many changes related to logging
  *        and exception handling.
  * @since 10/09/2004, Manchester changed to use knowledge bases
  */
int main(int argc, char* argv [])
{
  CALL ("main");

  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
   // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  try {
    env.options->setMode(Options::MODE_CLAUSIFY);

    // read the command line and interpret it
    Shell::CommandLine cl(argc,argv);
    cl.interpret(*env.options);

    PROCESS_TRACE_SPEC_STRING(env.options->traceSpecString());
    env.options->enableTracesAccordingToOptions();

    if(env.options->mode()!=Options::MODE_CLAUSIFY) {
      USER_ERROR("Only the \"clausify\" mode is supported");
    }

    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    clausifyMode();

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

  return vampireReturnValue;
} // main

