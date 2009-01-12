/**
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include <fstream>
#include <csignal>

#include "Debug/Tracer.hpp"

#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Lib/Vector.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/SubstitutionTree.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTP.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Refutation.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define SPIDER 1
#define SAVE_SPIDER_PROPERTIES 1

using namespace Shell;
using namespace Saturation;
using namespace Inferences;

void doProving()
{
  CALL("doProving()");

  env.signature = new Kernel::Signature;
  string inputFile = env.options->inputFile();
  ifstream input(inputFile.c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Property property;
  property.scan(units);

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

  ClauseIterator clauses=getStaticCastIterator<Clause*>(UnitList::Iterator(units));

  SaturationAlgorithmSP salg=SaturationAlgorithm::createFromOptions();
  salg->addClauses(clauses);

  SaturationResult sres(salg->saturate());
  sres.updateStatistics();
}

void outputResult()
{
  CALL("outputResult()");

  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    env.out << "Refutation found. Thanks to Tanya!\n";
    if (env.options->proof() != Options::PROOF_OFF) {
	Shell::Refutation refutation(env.statistics->refutation,
		env.options->proof() == Options::PROOF_ON);
	refutation.output(env.out);
    }
    break;
  case Statistics::TIME_LIMIT:
    env.out << "Time limit reached!\n";
    break;
  case Statistics::MEMORY_LIMIT:
#if VDEBUG
    Allocator::reportUsageByClasses();
#endif
    env.out << "Memory limit exceeded!\n";
    break;
  default:
    env.out << "Refutation not found!\n";
    break;
  }
  env.statistics->print();
}


void vampireMode()
{
  CALL("vampireMode()");
  env.out<<env.options->testId()<<" on "<<env.options->inputFile()<<endl;
  doProving();
  outputResult();
} // vampireMode

void spiderMode()
{
  CALL("spiderMode()");
  doProving();
  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    env.out << "+";
    break;
  case Statistics::TIME_LIMIT:
  case Statistics::MEMORY_LIMIT:
    env.out << "?";
    break;
  default:
    env.out << "-";
    break;
  }
  env.out<<env.options->testId()<<" "
    <<System::extractFileNameFromPath(env.options->inputFile())<<endl;
} // spiderMode


void explainException (Exception& exception)
{
  exception.cry(cout);
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

  System::setSignalHandlers();
   // create random seed for the random number generation
  Lib::Random::resetSeed();

  try {
    // read the command line and interpret it
    Options options;
    Shell::CommandLine cl(argc,argv);
    cl.interpret(options);
    Allocator::setMemoryLimit(options.memoryLimit()*1000000);

    Timer timer;
    timer.start();
    env.timer = &timer;
    Indexing::TermSharing sharing;
    env.sharing = &sharing;
    env.options = &options;
    Shell::Statistics statistics;
    env.statistics = &statistics;

    switch (options.mode())
      {
      case Options::MODE_VAMPIRE:
	vampireMode();
	break;
      case Options::MODE_SPIDER:
	spiderMode();
	break;
#if VDEBUG
      default:
  	ASSERTION_VIOLATION;
#endif
      }
#if CHECK_LEAKS
    delete env.signature;
    env.signature = 0;
    MemoryLeak leak;
    leak.release(units);
#endif
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (Exception& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (std::bad_alloc& _) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    cout << "Insufficient system memory" << '\n';
  }
//   delete env.allocator;
  return EXIT_SUCCESS;
} // main

