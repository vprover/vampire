/**
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include <iostream>
#include <ostream>
#include <fstream>
#include <csignal>

#include "Debug/Tracer.hpp"

#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Int.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/LiteralMiniIndex.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Grounding.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/TPTPLexer.hpp"
#include "Shell/TPTP.hpp"
#include "Shell/TPTPParser.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "SAT/DIMACS.hpp"
#include "SAT/SATClause.hpp"


#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define SPIDER 1
#define SAVE_SPIDER_PROPERTIES 1

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;

UnitList* globUnitList=0;

ClauseIterator getInputClauses(Property& property)
{
  env.signature = new Kernel::Signature;
  UnitList* units;
  {
    string inputFile = env.options->inputFile();
    ifstream input(inputFile.c_str());
    TPTPLexer lexer(input);
    TPTPParser parser(lexer);
    units = parser.units();
  }

//    if(units==0) {
//      cout<<"Empty units list!\n";
//    }

  property.scan(units);

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

  globUnitList=units;

  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );

}

void doProving()
{
  CALL("doProving()");
  try {
    Property property;

    ClauseIterator clauses=getInputClauses(property);

//    if(!clauses.hasNext()) {
//      cout<<"No clauses after preprocessing!\n";
//    }

    SaturationAlgorithmSP salg=SaturationAlgorithm::createFromOptions();
    salg->addInputClauses(clauses);

    SaturationResult sres(salg->saturate());
    sres.updateStatistics();
  } catch(MemoryLimitExceededException) {
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
    env.statistics->refutation=0;
    size_t limit=Allocator::getMemoryLimit();
    //add extra 1 MB to allow proper termination
    Allocator::setMemoryLimit(limit+1000000);
  } catch(TimeLimitExceededException) {
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
    env.statistics->refutation=0;
  }
}

void outputResult()
{
  CALL("outputResult()");

  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    env.out << "Refutation found. Thanks to Tanya!\n";
    if (env.options->proof() != Options::PROOF_OFF) {
//	Shell::Refutation refutation(env.statistics->refutation,
//		env.options->proof() == Options::PROOF_ON);
//	refutation.output(env.out);
      InferenceStore::instance()->outputProof(env.out, env.statistics->refutation);
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
  case Statistics::UNKNOWN:
    env.out << "Refutation not found with incomplete strategy!\n";
    break;
  default:
    env.out << "Refutation not found!\n";
    break;
  }
  env.statistics->print();
}


extern int gBDDTime;

void vampireMode()
{
  CALL("vampireMode()");
  env.out<<env.options->testId()<<" on "<<env.options->inputFile()<<endl;
  doProving();
  outputResult();
  cout<<"Time spent on BDDs: "<<gBDDTime<<endl;
} // vampireMode


void spiderMode()
{
  CALL("spiderMode()");
  bool noException=true;
  try {
    doProving();
  } catch(...) {
    noException=false;
    env.out << "! ";
  }
  if(noException) {
    switch (env.statistics->terminationReason) {
    case Statistics::REFUTATION:
      env.out << "+ ";
      break;
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
    case Statistics::UNKNOWN:
      env.out << "? ";
      break;
    default:
      env.out << "- ";
      break;
    }
  }
  env.out << " " << env.options->problemName();
  env.out << " " << env.timer->elapsedDeciseconds();
  env.out << " " << env.options->testId();
//  env.out << " " << gBDDTime;
  env.out << "\n";
} // spiderMode

void groundingMode()
{
  CALL("groundingMode()");

  try {
    Property property;
    ClauseIterator clauses=getInputClauses(property);

    if(property.equalityAtoms()) {
      ClauseList* eqAxioms=Grounding::addEqualityAxioms(property.positiveEqualityAtoms()!=0);
      clauses=pvi( getConcatenatedIterator(ClauseList::DestructiveIterator(eqAxioms), clauses) );
    }

    ClauseList* grounded=Grounding::simplyGround(clauses);
    SATClauseList* sgnd=SATClause::fromFOClauses(pvi( ClauseList::DestructiveIterator(grounded) ));
    DIMACS::outputProblem(sgnd, env.out);

  } catch(MemoryLimitExceededException) {
    env.out<<"Memory limit exceeded\n";
  } catch(TimeLimitExceededException) {
    env.out<<"Time limit exceeded\n";
  }
} // groundingMode


void explainException (Exception& exception)
{
  exception.cry(env.out);
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
  Lib::Random::setSeed(123456);

  try {
    // read the command line and interpret it
    Options options;
    Shell::CommandLine cl(argc,argv);
    cl.interpret(options);
    Allocator::setMemoryLimit(options.memoryLimit()*1048576);

    Lib::Random::setSeed(options.randomSeed());

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
    case Options::MODE_GROUNDING:
      groundingMode();
      break;
    case Options::MODE_SPIDER:
      spiderMode();
      break;
    case Options::MODE_VAMPIRE:
      vampireMode();
      break;
#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
    }
#if CHECK_LEAKS
    if(globUnitList) {
      MemoryLeak leak;
      leak.release(globUnitList);
    }
    delete env.signature;
    env.signature = 0;
#endif
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
    env.statistics->print();
  }
  catch (std::bad_alloc& _) {
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.out << "Insufficient system memory" << '\n';
  }
//   delete env.allocator;

  /*cout<<"good:\t"<<LiteralMiniIndex::goodPred<<endl;
  cout<<"bad:\t"<<LiteralMiniIndex::badPred<<endl;*/
  return EXIT_SUCCESS;
} // main

