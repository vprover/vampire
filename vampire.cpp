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
#include "Lib/MapToLIFO.hpp"
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
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "InstGen/IGAlgorithm.hpp"

#include "SAT/DIMACS.hpp"

#include "Shell/CASC/CASCMode.hpp"
#include "Shell/CASC/CLTBMode.hpp"
#include "Shell/CASC/SimpleLTBMode.hpp"
#include "Shell/CParser.hpp"
#include "Shell/CommandLine.hpp"
#include "Shell/EqualityProxy.hpp"
#include "Shell/Grounding.hpp"
#include "Shell/Normalisation.hpp"
#include "Shell/Options.hpp"
#include "Shell/Property.hpp"
#include "Saturation/ProvingHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Refutation.hpp"
#include "Shell/TheoryFinder.hpp"
#include "Shell/TPTP.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/SpecialTermElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define SPIDER 0
#define SAVE_SPIDER_PROPERTIES 0

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;
using namespace InstGen;

UnitList* globUnitList=0;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interupted by a SIGINT, value 3 is returned,
 * and in case of other signal we return 2. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case of an user error, we return value 4.
 *
 * In case Vampire was terminated by the timer, return value is
 * uncertain (but definitely not zero), probably it will be 134
 * (we terminate by a call to the @b abort() function in this case).
 */
int vampireReturnValue = 1;

ClauseIterator getProblemClauses()
{
  CALL("getInputClauses");
  
  UnitList* units=UIHelper::getInputUnits();

  TimeCounter tc2(TC_PREPROCESSING);

  env.statistics->phase=Statistics::PROPERTY_SCANNING;
  Property* property = Property::scan(units);
  Preprocess prepro(*property,*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(units);
  globUnitList=units;

  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );
}

void doProving()
{
  CALL("doProving()");
  ClauseIterator clauses=getProblemClauses();
  ProvingHelper::runVampireSaturation(clauses);
}

/**
 * Read a problem and output profiling information about it.
 * @since 03/08/2008 Torrevieja
 */
void profileMode()
{
  CALL("profileMode()");

  string inputFile = env.options->inputFile();
  istream* input;
  if(inputFile=="") {
    input=&cin;
  }
  else {
    input=new ifstream(inputFile.c_str());
    if(input->fail()) {
      USER_ERROR("Cannot open input file: "+inputFile);
    }
  }

  UnitList* units = Parse::TPTP::parse(*input);
  if(inputFile!="") {
    delete static_cast<ifstream*>(input);
    input=0;
  }

  Property* property = Property::scan(units);
  TheoryFinder tf(units,property);
  Preprocess prepro(*property,*env.options);
  tf.search();

  env.beginOutput();
  env.out() << property->categoryString() << ' '
       << property->props() << ' '
       << property->atoms() << "\n";
  env.endOutput();

  //we have succeeded with the profile mode, so we'll terminate with zero return value
  vampireReturnValue=0;
  delete property;
} // profileMode

void programAnalysisMode()
{
  CALL("programAnalysisMode()");

#if 0
  string inputFile = env.options->inputFile();
  istream* input;
  if(inputFile=="") {
    input=&cin;
  } else {
    cout << "Analyzing " << inputFile << "...\n";
    input=new ifstream(inputFile.c_str());
    if(input->fail()) {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
  }
  string progString("");
  while (!input->eof()) {
    string inp;
    getline(*input,inp);
    progString += inp + '\n';
  }
  // cout << progString;

  CParser parser(progString.c_str());
  parser.tokenize();
  //  parser.output(cout);
#else
  INVALID_OPERATION("program analysis currently not supported");
#endif
  vampireReturnValue=0;
} // programAnalysisMode

void vampireMode()
{
  CALL("vampireMode()");

  if(env.options->mode()==Options::MODE_CONSEQUENCE_ELIMINATION) {
    env.options->setUnusedPredicateDefinitionRemoval(false);
    env.options->setPropositionalToBDD(false);
  }

  string inputFile = env.options->inputFile();
  istream* input;
  if(inputFile=="") {
    input=&cin;
  }
  else {
    input=new ifstream(inputFile.c_str());
    if(input->fail()) {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
  }

  doProving();

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

#if SATISFIABLE_IS_SUCCESS
  if(env.statistics->terminationReason==Statistics::REFUTATION ||
      env.statistics->terminationReason==Statistics::SATISFIABLE) {
#else
    if(env.statistics->terminationReason==Statistics::REFUTATION) {
#endif
    vampireReturnValue=0;
  }
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

  env.beginOutput();
  if(noException) {
    switch (env.statistics->terminationReason) {
    case Statistics::REFUTATION:
      reportSpiderStatus('+');
      vampireReturnValue=0;
      break;
    case Statistics::TIME_LIMIT:
    case Statistics::MEMORY_LIMIT:
    case Statistics::UNKNOWN:
    case Statistics::REFUTATION_NOT_FOUND:
      reportSpiderStatus('?');
      break;
    case Statistics::SATISFIABLE:
      reportSpiderStatus('-');
#if SATISFIABLE_IS_SUCCESS
      vampireReturnValue=0;
#endif
      break;
    default:
      ASSERTION_VIOLATION;
    }
    env.statistics->print(env.out());
  }
  else {
    reportSpiderFail();
  }
  env.endOutput();
} // spiderMode

void clausifyMode()
{
  CALL("clausifyMode()");

  CompositeISE simplifier;
  simplifier.addFront(ImmediateSimplificationEngineSP(new TrivialInequalitiesRemovalISE()));
  simplifier.addFront(ImmediateSimplificationEngineSP(new TautologyDeletionISE()));
  simplifier.addFront(ImmediateSimplificationEngineSP(new DuplicateLiteralRemovalISE()));

  ClauseIterator cit = getProblemClauses();
  env.beginOutput();
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
  vampireReturnValue=0;
} // clausifyMode

void axiomSelectionMode()
{
  CALL("axiomSelectionMode()");

  env.options->setSineSelection(Options::SS_AXIOMS);

  UnitList* units=UIHelper::getInputUnits();

  SpecialTermElimination().apply(units);

  // reorder units
  if (env.options->normalize()) {
    env.statistics->phase=Statistics::NORMALIZATION;
    Normalisation norm;
    units = norm.normalise(units);
  }

  env.statistics->phase=Statistics::SINE_SELECTION;
  SineSelector().perform(units);

  env.statistics->phase=Statistics::FINALIZATION;

  UnitList::Iterator uit(units);
  env.beginOutput();
  while (uit.hasNext()) {
    Unit* u=uit.next();
    env.out() << TPTP::toString(u) << "\n";
  }
  env.endOutput();

  //we have successfully output the selected units, so we'll terminate with zero return value
  vampireReturnValue=0;
}

void groundingMode()
{
  CALL("groundingMode()");

  try {

    string inputFile = env.options->inputFile();
    istream* input;
    if(inputFile=="") {
      input=&cin;
    } else {
      input=new ifstream(inputFile.c_str());
    }
    UnitList* units = Parse::TPTP::parse(*input);
    if(inputFile!="") {
      delete static_cast<ifstream*>(input);
      input=0;
    }

    Property* property = Property::scan(units);
    Preprocess prepro(*property,*env.options);
    prepro.preprocess(units);
    delete property;

    property->scan(units);
    globUnitList=units;
    ClauseIterator clauses=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );

    if(property->equalityAtoms()) {
      ClauseList* eqAxioms=Grounding::getEqualityAxioms(property->positiveEqualityAtoms()!=0);
      clauses=pvi(getConcatenatedIterator(ClauseList::DestructiveIterator(eqAxioms),clauses));
    }

    MapToLIFO<Clause*, SATClause*> insts;
    Grounding gnd;
    SATClause::NamingContext nameCtx;

    while(clauses.hasNext()) {
      Clause* cl=clauses.next();
      ClauseList* grounded=gnd.ground(cl);
      SATClauseList* sGrounded=0;
      while(grounded) {
	Clause* gcl=ClauseList::pop(grounded);
	SATClauseList::push(SATClause::fromFOClause(nameCtx, gcl), sGrounded);
      }
      insts.pushManyToKey(cl, sGrounded);
    }
    env.beginOutput();
    DIMACS::outputGroundedProblem(insts, nameCtx, env.out());
    env.endOutput();

  } catch(MemoryLimitExceededException) {
    env.beginOutput();
    env.out()<<"Memory limit exceeded\n";
    env.endOutput();
  } catch(TimeLimitExceededException) {
    env.beginOutput();
    env.out()<<"Time limit exceeded\n";
    env.endOutput();
  }
} // groundingMode

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
    // read the command line and interpret it
    Shell::CommandLine cl(argc,argv);
    cl.interpret(*env.options);

    if(env.options->showOptions()) {
      env.beginOutput();
      env.options->output(env.out());
      env.endOutput();
    }

    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::MODE_AXIOM_SELECTION:
      axiomSelectionMode();
      break;
    case Options::MODE_GROUNDING:
      groundingMode();
      break;
    case Options::MODE_SPIDER:
      spiderMode();
      break;
    case Options::MODE_CONSEQUENCE_ELIMINATION:
    case Options::MODE_VAMPIRE:
      vampireMode();
      break;
    case Options::MODE_CASC:
      if(Shell::CASC::CASCMode::perform(argc, argv)) {
	//casc mode succeeded in solving the problem, so we return zero
	vampireReturnValue=0;
      }
      break;
    case Options::MODE_CASC_SIMPLE_LTB:
    {
      Shell::CASC::SimpleLTBMode sltbm;
      sltbm.perform();
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue=0;
      break;
    }
    case Options::MODE_CASC_LTB:
    {
      Shell::CASC::CLTBMode::perform();
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue=0;
      break;
    }
    case Options::MODE_CLAUSIFY:
      clausifyMode();
      break;
    case Options::MODE_PROFILE:
      profileMode();
      break;
    case Options::MODE_PROGRAM_ANALYSIS:
      programAnalysisMode();
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
    vampireReturnValue = 4;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException& exception) {
    vampireReturnValue = 4;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
    vampireReturnValue = 4;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    explainException(exception);
    env.statistics->print(env.out());
    env.endOutput();
  }
  catch (std::bad_alloc& _) {
    vampireReturnValue = 4;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    env.out() << "Insufficient system memory" << '\n';
    env.endOutput();
  }
//   delete env.allocator;

  return vampireReturnValue;
} // main

