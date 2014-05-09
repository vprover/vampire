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

#include "Lib/RCPtr.hpp"


#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/TermSharing.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Inferences/TautologyDeletionISE.hpp"

#include "InstGen/IGAlgorithm.hpp"

#include "SAT/DIMACS.hpp"

#include "CASC/CASCMode.hpp"
#include "CASC/CLTBMode.hpp"
#include "CASC/CMZRMode.hpp"
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
#include "Shell/TPTPPrinter.hpp"
#include "Parse/TPTP.hpp"
#include "Shell/SpecialTermElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "SAT/LingelingInterfacing.hpp"
#include "SAT/TWLSolver.hpp"

#if IS_LINGVA
#include "Program/Lingva.hpp"
#endif

#if GNUMP
#include "Solving/Solver.hpp"

using namespace Shell;
using namespace Solving;
#endif

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

Problem* globProblem = 0;
UnitList* globUnitList=0;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interupted by a SIGINT, value
 * VAMP_RESULT_STATUS_SIGINT is returned,
 * and in case of other signal we return VAMP_RESULT_STATUS_OTHER_SIGNAL. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case of an unhandled exception or user error, we return value
 * VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION.
 *
 * In case Vampire was terminated by the timer, return value is
 * uncertain (but definitely not zero), probably it will be 134
 * (we terminate by a call to the @b abort() function in this case).
 */
int vampireReturnValue = VAMP_RESULT_STATUS_UNKNOWN;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If execution was interupted by a SIGINT, value 3 is returned,
 * and in case of other signal we return 2. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case execution was terminated by the timer, return value is 1.
 * (see @c timeLimitReached() in Lib/Timer.cpp)
 */
int g_returnValue = 1;

Problem* getPreprocessedProblem()
{
  CALL("getInputClauses");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(*prb);
  globProblem = prb;

  return prb;
} // getPreprocessedProblem

void explainException(Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

void doProving()
{
  CALL("doProving()");
  ScopedPtr<Problem> prb(getPreprocessedProblem());
  ProvingHelper::runVampireSaturation(*prb, *env.options);
}

/**
 * Read a problem and output profiling information about it.
 * @since 03/08/2008 Torrevieja
 */
void profileMode()
{
  CALL("profileMode()");

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  Property* property = prb->getProperty();
  TheoryFinder tf(prb->units(), property);
  Preprocess prepro(*env.options);
  tf.search();

  env.beginOutput();
  env.out() << property->categoryString() << ' ' << property->props() << ' '
	  << property->atoms() << "\n";
  env.endOutput();

  //we have succeeded with the profile mode, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // profileMode

void programAnalysisMode()
{
  CALL("programAnalysisMode()");

  // create random seed for the random number generation

#if 0
  string inputFile = env.options->inputFile();
  istream* input;
  if (inputFile=="") {
    input=&cin;
  } else {
    cout << "Analyzing " << inputFile << "...\n";
    input=new ifstream(inputFile.c_str());
    if (input->fail()) {
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
#endif

#if IS_LINGVA
  Lib::Random::setSeed(123456);
  int time = env.options->timeLimitInDeciseconds();
  env.options->setMode(Options::MODE_VAMPIRE);
  Allocator::setMemoryLimit(1024u * 1048576ul);

  string inputFile = env.options->inputFile();
  if (inputFile == "") {
    USER_ERROR("Cannot open problem file: "+inputFile);
  }
  else {
    //default time limit 10 seconds
    if (time == 0) {
      env.options->setTimeLimitInDeciseconds(100);
    }
    Program::RunLingva lingva;
    lingva.run();
  }

#else
  INVALID_OPERATION("program analysis currently not supported");
#endif
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // programAnalysisMode


void outputResult(ostream& out) {
  CALL("outputResult");

  switch(env.statistics->terminationReason) {
  case Statistics::UNKNOWN:
    cout<<"unknown"<<endl;
    break;
  case Statistics::SATISFIABLE:
    cout<<"sat"<<endl;
#if GNUMP
    UIHelper::outputAssignment(*env.statistics->satisfyingAssigment, cout);
#endif //GNUMP
    break;
  case Statistics::REFUTATION:
    cout<<"unsat"<<endl;
    break;
#if VDEBUG
  default:
    ASSERTION_VIOLATION; //these outcomes are not reachable with the current implementation
#endif
  }
  env.statistics->print(env.out());
}



void boundPropagationMode(){
#if GNUMP
  CALL("boundPropagationMode::doSolving()");

  if (env.options->bpStartWithPrecise()) {
	  switchToPreciseNumbers();
  }
  if (env.options->bpStartWithRational()){
	  switchToRationalNumbers();
  }

  ConstraintRCList* constraints(UIHelper::getPreprocessedConstraints(*env.options));

#if 0
  ConstraintRCList::Iterator ite(constraints);
  while(ite.hasNext())
      std::cout<<"preproc: "<<ite.next()->toString()<<"\n";
#endif

  start:
  try
  {
    env.statistics->phase = Statistics::SOLVING;
    TimeCounter tc(TC_SOLVING);
    Solver solver(env.signature->vars(), *env.options, *env.statistics);
    solver.load(constraints);
    solver.solve();
  }
  catch (Solver::NumberImprecisionException) {
    if (usingPreciseNumbers()) {
      INVALID_OPERATION("Imprecision error when using precise numbers.");
    }
    else {
      env.statistics->switchToPreciseTimeInMs = env.timer->elapsedMilliseconds();
      switchToPreciseNumbers();
      //switchToRationalNumbers();
      ASS(usingPreciseNumbers());
      goto start;
    }
  }
  catch (TimeLimitExceededException){
      env.statistics->phase = Statistics::FINALIZATION;
      env.statistics->terminationReason = Statistics::TIME_LIMIT;
    }
  env.statistics->phase = Statistics::FINALIZATION;
#endif
}

void solverMode()
{
  CALL("solverMode()");
#if GNUMP
  //adjust vampire options in order to serve the purpose of bound propagation
  if ( env.options->proof() == env.options->PROOF_ON ) {
    env.options->setProof(env.options->PROOF_OFF);
  }

  //this ensures the fact that int's read in smtlib file are treated as reals
  env.options->setSmtlibConsiderIntsReal(true);

  boundPropagationMode();

  env.beginOutput();
  outputResult(env.out());
  env.endOutput();

  if (env.statistics->terminationReason==Statistics::REFUTATION
      || env.statistics->terminationReason==Statistics::SATISFIABLE) {
    g_returnValue=0;
  }
#endif
} // solverMode

/**
 * This mode only preprocesses the input using the current preprocessing
 * options and outputs it to stdout. It is useful for either preprocessing
 * per se or also for converting one syntax to another. For the latter, the input
 * and the output syntaxes must be set to different values. Note that for
 * simply translating one syntax to another, output mode is the right one.
 * 
 * @author Andrei Voronkov
 * @since 02/07/2013 Manchester
 */
void preprocessMode()
{
  CALL("preprocessMode()");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  // preprocess without clausification
  Preprocess prepro(*env.options);
  prepro.turnClausifierOff();
  prepro.preprocess(*prb);

  env.beginOutput();
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());
  while (units.hasNext()) {
    Unit* u = units.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // preprocessMode

/**
 * This mode only outputs the input problem. It is useful for converting
 * one syntax to another.
 * @author Laura Kovacs and Andrei Voronkov
 * @since 02/07/2013 Gothenburg and Manchester
 */
void outputMode()
{
  CALL("outputMode()");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  env.beginOutput();
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());
  while (units.hasNext()) {
    Unit* u = units.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // outputMode

SATClauseList* getInputClauses(const char* fname, unsigned& varCnt)
{
  CALL("getInputClauses");
  TimeCounter tc(TC_PREPROCESSING);
  unsigned maxVar;
  SATClauseIterator cit=( DIMACS::parse(fname, maxVar) );
  varCnt=maxVar+1;

  SATClauseList* clauses = 0;
  SATClauseList::pushFromIterator(cit, clauses);
  return clauses;
}

void satSolverMode()
{
  CALL("satSolverMode()");
  TimeCounter tc(TC_SAT_SOLVER);
  SATSolverSCP solver(new TWLSolver(*env.options, false));

  //get the clauses; 
  SATClauseList* clauses;
  unsigned varCnt=0;

  SATSolver::Status res; 
  
  clauses = getInputClauses(env.options->inputFile().c_str(), varCnt);
  cout<<"we have : "<<varCnt << " variables\n";
  
  solver->ensureVarCnt(varCnt);
  
  //add all the clauses to the solver 
  solver->addClauses(pvi(SATClauseList::Iterator(clauses)));
  res = solver->getStatus();

  env.statistics->phase = Statistics::FINALIZATION;

  switch(res) {
  case SATSolver::SATISFIABLE:
    cout<<"SATISFIABLE\n";
    env.statistics->terminationReason = Statistics::SAT_SATISFIABLE;
    break;
  case SATSolver::UNSATISFIABLE:
    cout<<"UNSATISFIABLE\n";
    env.statistics->terminationReason = Statistics::SAT_UNSATISFIABLE;
    break;
  case SATSolver::UNKNOWN:
    cout<<"Unknown\n";
    break;
  }

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();
#if SATISFIABLE_IS_SUCCESS
  if (env.statistics->terminationReason == Statistics::SAT_UNSATISFIABLE
      || env.statistics->terminationReason == Statistics::SAT_SATISFIABLE) {
#else
    if (env.statistics->terminationReason==Statistics:SAT_UNSATISFIABLE) {
#endif
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
  }

}
void vampireMode()
{
  CALL("vampireMode()");

  if (env.options->mode() == Options::MODE_CONSEQUENCE_ELIMINATION) {
    env.options->setUnusedPredicateDefinitionRemoval(false);
  }

  string inputFile = env.options->inputFile();
  istream* input;
  if (inputFile == "") {
    input = &cin;
  } else {
    input = new ifstream(inputFile.c_str());
    if (input->fail()) {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
  }

  doProving();

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

#if SATISFIABLE_IS_SUCCESS
  if (env.statistics->terminationReason == Statistics::REFUTATION
      || env.statistics->terminationReason == Statistics::SATISFIABLE) {
#else
    if (env.statistics->terminationReason==Statistics::REFUTATION) {
#endif
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
  }
} // vampireMode

void spiderMode()
{
  CALL("spiderMode()");
  bool noException = true;
  try {
    doProving();
  } catch (...) {
    noException = false;
  }

  env.beginOutput();
  if (noException) {
    switch (env.statistics->terminationReason) {
    case Statistics::REFUTATION:
      reportSpiderStatus('+');
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
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
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
#endif
      break;
    default:
      ASSERTION_VIOLATION;
    }
    env.statistics->print(env.out());
  } else {
    reportSpiderFail();
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
  }
  env.endOutput();
} // spiderMode

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
    Clause* cl = cit.next();
    cl = simplifier.simplify(cl);
    if (!cl) {
      continue;
    }
    env.out() << TPTPPrinter::toString(cl) << "\n";
  }
  env.endOutput();

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // clausifyMode

void axiomSelectionMode()
{
  CALL("axiomSelectionMode()");

  env.options->setSineSelection(Options::SS_AXIOMS);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  if (prb->hasSpecialTermsOrLets()) {
    SpecialTermElimination().apply(*prb);
  }

  // reorder units
  if (env.options->normalize()) {
    env.statistics->phase = Statistics::NORMALIZATION;
    Normalisation norm;
    norm.normalise(*prb);
  }

  env.statistics->phase = Statistics::SINE_SELECTION;
  SineSelector(*env.options).perform(*prb);

  env.statistics->phase = Statistics::FINALIZATION;

  UnitList::Iterator uit(prb->units());
  env.beginOutput();
  while (uit.hasNext()) {
    Unit* u = uit.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  //we have successfully output the selected units, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
}

void groundingMode()
{
  CALL("groundingMode()");

  try {
    ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

    Preprocess prepro(*env.options);
    prepro.preprocess(*prb);

    ClauseIterator clauses = prb->clauseIterator();

    if (prb->hasEquality()) {
      ClauseList* eqAxioms = Grounding::getEqualityAxioms(
	      prb->getProperty()->positiveEqualityAtoms() != 0);
      clauses = pvi(
	      getConcatenatedIterator(ClauseList::DestructiveIterator(eqAxioms),
		      clauses));
    }

    MapToLIFO<Clause*, SATClause*> insts;
    Grounding gnd;
    SATClause::NamingContext nameCtx;

    while (clauses.hasNext()) {
      Clause* cl = clauses.next();
      ClauseList* grounded = gnd.ground(cl);
      SATClauseList* sGrounded = 0;
      while (grounded) {
	Clause* gcl = ClauseList::pop(grounded);
	SATClauseList::push(SATClause::fromFOClause(nameCtx, gcl), sGrounded);
      }
      insts.pushManyToKey(cl, sGrounded);
    }
    env.beginOutput();
    DIMACS::outputGroundedProblem(insts, nameCtx, env.out());
    env.endOutput();

  } catch (MemoryLimitExceededException) {
    env.beginOutput();
    env.out() << "Memory limit exceeded\n";
    env.endOutput();
  } catch (TimeLimitExceededException) {
    env.beginOutput();
    env.out() << "Time limit exceeded\n";
    env.endOutput();
  }
} // groundingMode

/**
 * The main function.
 * @since 03/12/2003 many changes related to logging
 *        and exception handling.
 * @since 10/09/2004, Manchester changed to use knowledge bases
 */
int main(int argc, char* argv[])
{
  CALL ("main");

//#if IS_LINGVA
//    env.options->setMode(Options::MODE_PROGRAM_ANALYSIS);
//#endif

  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
  // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  try {
    // read the command line and interpret it
    Shell::CommandLine cl(argc, argv);
    cl.interpret(*env.options);

    if (env.options->showOptions()) {
      env.beginOutput();
      env.options->output(env.out());
      env.endOutput();
    }

    Allocator::setMemoryLimit(env.options->memoryLimit() * 1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::MODE_AXIOM_SELECTION:
      axiomSelectionMode();
      break;
    case Options::MODE_GROUNDING:
      groundingMode();
      break;
    case Options::MODE_SOLVER:
#if GNUMP
     solverMode();
#else
     NOT_IMPLEMENTED;
#endif
      break;
    case Options::MODE_SPIDER:
      spiderMode();
      break;
    case Options::MODE_CONSEQUENCE_ELIMINATION:
    case Options::MODE_VAMPIRE:
      vampireMode();
      break;
    case Options::MODE_CASC:
      if (CASC::CASCMode::perform(argc, argv)) {
	//casc mode succeeded in solving the problem, so we return zero
	vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;
    case Options::MODE_CASC_SAT:
      CASC::CASCMode::makeSat();
      if (CASC::CASCMode::perform(argc, argv)) {
	//casc mode succeeded in solving the problem, so we return zero
	vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;
    case Options::MODE_CASC_EPR:
      CASC::CASCMode::makeEPR();
      if (CASC::CASCMode::perform(argc, argv)) {
	//casc mode succeeded in solving the problem, so we return zero
	vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;
    case Options::MODE_CASC_LTB: {
      CASC::CLTBMode::perform();
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    }
    case Options::MODE_CASC_MZR: {
      CASC::CMZRMode::perform();
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    }

    case Options::MODE_CLAUSIFY:
      clausifyMode();
      break;

    case Options::MODE_OUTPUT:
      outputMode();
      break;

    case Options::MODE_PROFILE:
      profileMode();
      break;

    case Options::MODE_PROGRAM_ANALYSIS:
      std::cout<<"Program analysis mode "<<std::endl;
      programAnalysisMode();
      break;
   
    case Options::MODE_PREPROCESS:
      preprocessMode();
      break;

    case Options::MODE_SAT:
      satSolverMode();
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
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
  }
#endif
  catch (UserErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  } catch (Exception& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    explainException(exception);
    env.statistics->print(env.out());
    env.endOutput();
  } catch (std::bad_alloc& _) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
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

