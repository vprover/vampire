/**
 * @file alucard.cpp. Lightweight testing version of Dracula.
 */

#include <fstream>
#include <csignal>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Lib/Vector.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/LiteralSelector.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTP.hpp"
#include "Shell/TPTPParser.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/TheoryFinder.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/AWPassiveClauseContainer.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/BinaryResolution.hpp"
#include "Inferences/AtomicClauseForwardSubsumption.hpp"
#include "Inferences/SLQueryForwardSubsumption.hpp"


#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;
using namespace Inferences;

SaturationResult brSaturate(ClauseIterator clauses)
{
  AWPassiveClauseContainer passiveContainer;
  passiveContainer.setAgeWeightRatio(1,1);

  BinaryResolution generator;
  CompositeFSE fwSimplifier;
  DuplicateLiteralRemovalFSE dlrFSE;
  TrivialInequalitiesRemovalFSE tirFSE;
  AtomicClauseForwardSubsumption acfsFSE;
  SLQueryForwardSubsumption slfsFSE;
//  fwSimplifier.addFront(&acfsFSE);
  fwSimplifier.addFront(&slfsFSE);
  fwSimplifier.addFront(&tirFSE);
  fwSimplifier.addFront(&dlrFSE);

  DummyBSE bwSimplifier;
  EagerLiteralSelector eselector;
  LightestNegativeLiteralSelection lselector;
  HeaviestNegativeLiteralSelection hselector;

  DiscountSA salg(&passiveContainer, &hselector);
  salg.setGeneratingInferenceEngine(&generator);
  salg.setForwardSimplificationEngine(&fwSimplifier);
  salg.setBackwardSimplificationEngine(&bwSimplifier);

  salg.addClauses(clauses);

  return salg.saturate();
}

void doProving()
{
  CALL("doProving()");

  env.signature = new Kernel::Signature;
  ifstream input(env.options->inputFile().c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Property property;
  property.scan(units);

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

  ClauseIterator clauses=getStaticCastIterator<Clause*>(UnitList::Iterator(units));

  try {

    SaturationResult res=brSaturate(clauses);
    res.updateStatistics();

    throw 1;
  } catch (...) {
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
      env.out << "Memory limit exceeded!\n";
#if VDEBUG
      Allocator::reportUsageByClasses();
#endif
      break;
    default:
      env.out << "Refutation not found!\n";
      break;
    }
    env.out << "Active clauses: "<<env.statistics->activeClauses<<endl;
    env.out << "Passive clauses: "<<env.statistics->passiveClauses<<endl;
    env.out << "Generated clauses: "<<env.statistics->generatedClauses<<endl;
    env.out << "Duplicate literals: "<<env.statistics->duplicateLiterals<<endl;
    env.out << "Trivial inequalities: "<<env.statistics->trivialInequalities<<endl;
    env.out << "Forward subsumptions: "<<env.statistics->forwardSubsumed<<endl;
    try{
      throw;
    } catch (int) {}
  }

#if CHECK_LEAKS
  delete env.signature;
  env.signature = 0;
  MemoryLeak leak;
  leak.release(units);
#endif
} // ruleMode

/**
 * Print an explanation about exception to cout either as a text or
 * as XML, depending on the environment.
 * @since 10/08/2005 Redmond
 */
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

    doProving();

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

