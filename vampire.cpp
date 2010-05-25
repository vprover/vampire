/**
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include <string>
#include <iostream>
#include <ostream>
#include <fstream>
#include <csignal>

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Random.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Lib/List.hpp"
#include "Lib/Vector.hpp"
#include "Lib/System.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/LiteralMiniIndex.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/Grounding.hpp"
#include "Shell/Interpolants.hpp"
#include "Shell/LaTeX.hpp"
#include "Shell/LispLexer.hpp"
#include "Shell/LispParser.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/TheoryFinder.hpp"
#include "Shell/SimplifyProver.hpp"
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

#define SPIDER 0
#define SAVE_SPIDER_PROPERTIES 0

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;

UnitList* globUnitList=0;

ClauseIterator getInputClauses()
{
  CALL("getInputClauses");
  
  Property property;

  UnitList* units;
  {
    TimeCounter tc1(TC_PARSING);

    string inputFile = env.options->inputFile();

    istream* input;
    if(inputFile=="") {
      input=&cin;
    } else {
      input=new ifstream(inputFile.c_str());
    }


    env.statistics->phase=Statistics::PARSING;
    switch (env.options->inputSyntax()) {
    case Options::IS_SIMPLIFY:
    {
      Shell::LispLexer lexer(*input);
      Shell::LispParser parser(lexer);
      LispParser::Expression* expr = parser.parse();
      SimplifyProver simplify;
      units = simplify.units(expr);
    }
    break;
    case Options::IS_TPTP:
    {
      TPTPLexer lexer(*input);
      TPTPParser parser(lexer);
      units = parser.units();
    }
    break;
    }

    if(inputFile!="") {
      delete static_cast<ifstream*>(input);
      input=0;
    }
  }

  TimeCounter tc2(TC_PREPROCESSING);

  env.statistics->phase=Statistics::PROPERTY_SCANNING;
  property.scan(units);
  Preprocess prepro(property,*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(units);

  globUnitList=units;

  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );
}

void doProving()
{
  CALL("doProving()");
  try {
    ClauseIterator clauses=getInputClauses();
    Unit::onPreprocessingEnd();

    env.statistics->phase=Statistics::SATURATION;
    SaturationAlgorithmSP salg=SaturationAlgorithm::createFromOptions();
    salg->addInputClauses(clauses);

    SaturationResult sres(salg->saturate());
    env.statistics->phase=Statistics::FINALIZATION;
    sres.updateStatistics();
  }
  catch(MemoryLimitExceededException) {
    env.statistics->terminationReason=Statistics::MEMORY_LIMIT;
    env.statistics->refutation=0;
    size_t limit=Allocator::getMemoryLimit();
    //add extra 1 MB to allow proper termination
    Allocator::setMemoryLimit(limit+1000000);
  }
  catch(TimeLimitExceededException) {
    env.statistics->terminationReason=Statistics::TIME_LIMIT;
    env.statistics->refutation=0;
  }
}

void outputResult()
{
  CALL("outputResult()");

  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    env.out << "Refutation found. Thanks to "
	    << env.options->thanks() << "!\n";
    if (env.options->proof() != Options::PROOF_OFF) {
//	Shell::Refutation refutation(env.statistics->refutation,
//		env.options->proof() == Options::PROOF_ON);
//	refutation.output(env.out);
      InferenceStore::instance()->outputProof(env.out, env.statistics->refutation);
    }
    if(env.options->showInterpolant()) {
      ASS(env.statistics->refutation->isClause());
      Formula* interpolant=Interpolants::getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      env.out << "Interpolant: " << interpolant->toString() << endl;
    }
    if(env.options->latexOutput()!="off") {
      ofstream latexOut(env.options->latexOutput().c_str());

      LaTeX formatter;
      latexOut<<formatter.refutationToString(env.statistics->refutation);
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
  case Statistics::REFUTATION_NOT_FOUND:
    if(env.options->complete()) {
      ASS_EQ(env.options->saturationAlgorithm(), Options::LRS);
      env.out << "Refutation not found, LRS age and weight limit was active for some time!\n";
    } else {
      env.out << "Refutation not found with incomplete strategy!\n";
    }
    break;
  case Statistics::SATISFIABLE:
    env.out << "Refutation not found!\n";
    break;
  case Statistics::UNKNOWN:
    env.out << "Unknown reason of termination!\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  env.statistics->print();

}

/**
 * Read a problem and output profiling information about it.
 * @since 03/08/2008 Torrevieja
 */
void profileMode()
{
  CALL("profileMode()");

  Property property;
  env.signature = new Kernel::Signature;
  UnitList* units;
  string inputFile = env.options->inputFile();
  istream* input;
  if(inputFile=="") {
    input=&cin;
  }
  else {
    input=new ifstream(inputFile.c_str());
  }

  TPTPLexer lexer(*input);
  TPTPParser parser(lexer);
  units = parser.units();
  if(inputFile!="") {
    delete static_cast<ifstream*>(input);
    input=0;
  }

  property.scan(units);
  TheoryFinder tf(units,&property);
  Preprocess prepro(property,*env.options);
  tf.search();
  cout << property.categoryString() << ' '
       << property.props() << ' '
       << property.atoms() << "\n";
} // profileMode

void vampireMode()
{
  CALL("vampireMode()");
  env.out<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  doProving();
  outputResult();
} // vampireMode


void spiderMode()
{
  CALL("spiderMode()");
  bool noException=true;
  try {
    doProving();
  }
  catch(...) {
    noException=false;
  }

  if(noException) {
    switch (env.statistics->terminationReason) {
    case Statistics::REFUTATION:
      reportSpiderStatus('+');
      break;
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
    case Statistics::UNKNOWN:
    case Statistics::REFUTATION_NOT_FOUND:
      reportSpiderStatus('?');
      break;
    case Statistics::SATISFIABLE:
      reportSpiderStatus('-');
      break;
    default:
      ASSERTION_VIOLATION;
    }
    env.statistics->print();
  }
  else {
    reportSpiderFail();
  }
} // spiderMode

void clausifyMode()
{
  CALL("clausifyMode()");

  CompositeISE simplifier;
  simplifier.addFront(ImmediateSimplificationEngineSP(new TrivialInequalitiesRemovalISE()));
  simplifier.addFront(ImmediateSimplificationEngineSP(new TautologyDeletionISE()));
  simplifier.addFront(ImmediateSimplificationEngineSP(new DuplicateLiteralRemovalISE()));

  ClauseIterator cit = getInputClauses();
  while (cit.hasNext()) {
    Clause* cl=cit.next();
    cl=simplifier.simplify(cl);
    if(!cl) {
      continue;
    }
    cout << TPTP::toString(cl) << "\n";
  }
} // clausifyMode

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

  Timer::initTimer();

  System::setSignalHandlers();
   // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  try {
    env.signature = new Kernel::Signature;
    
    // read the command line and interpret it
    Shell::CommandLine cl(argc,argv);
    cl.interpret(*env.options);

    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::MODE_GROUNDING:
      USER_ERROR("Use the vground executable for grounding.");
      break;
    case Options::MODE_SPIDER:
      spiderMode();
      break;
    case Options::MODE_CONSEQUENCE_FINDING:
    case Options::MODE_VAMPIRE:
      vampireMode();
      break;
    case Options::MODE_CASC:
      USER_ERROR("CASC mode is not implemented");
      break;
    case Options::MODE_CLAUSIFY:
      clausifyMode();
      break;
    case Options::MODE_PROFILE:
      profileMode();
      break;
    case Options::MODE_RULE:
      USER_ERROR("Rule mode is not implemented");
      break;
    default:
      USER_ERROR("Unsupported mode");
    }
#if CHECK_LEAKS
    if (globUnitList) {
      MemoryLeak leak;
      leak.release(globUnitList);
    }
    delete env.signature;
    env.signature = 0;
#endif
  }
#if VDEBUG
  catch (Debug::AssertionViolationException& exception) {
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException& exception) {
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
    env.statistics->print();
  }
  catch (std::bad_alloc& _) {
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.out << "Insufficient system memory" << '\n';
  }
//   delete env.allocator;

  return EXIT_SUCCESS;
} // main

