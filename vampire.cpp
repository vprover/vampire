
/*
 * File vampire.cpp.
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
 * @file vampire.cpp. Implements the top-level procedures of Vampire.
 */

#include <iostream>
#include <ostream>
#include <fstream>
#include <csignal>

#if VZ3
#include "z3++.h"
#endif

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
#include "Lib/VString.hpp"
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

#include "CASC/PortfolioMode.hpp"
#include "CASC/CLTBMode.hpp"
#include "CASC/CLTBModeLearning.hpp"
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
#include "Shell/FOOLElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/LaTeX.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "SAT/MinisatInterfacing.hpp"
#include "SAT/MinisatInterfacingNewSimp.hpp"
#include "SAT/TWLSolver.hpp"
#include "SAT/Preprocess.hpp"

#include "FMB/ModelCheck.hpp"

#if GNUMP
#include "Solving/Solver.hpp"

using namespace Shell;
using namespace Solving;
#endif

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define USE_SPIDER 0
#define SAVE_SPIDER_PROPERTIES 0

using namespace Shell;
using namespace SAT;
using namespace Saturation;
using namespace Inferences;
using namespace InstGen;

/**
 * Return value is non-zero unless we were successful.
 *
 * Being successful for modes that involve proving means that we have
 * either found refutation or established satisfiability.
 *
 *
 * If Vampire was interrupted by a SIGINT, value
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
 * If execution was interrupted by a SIGINT, value 3 is returned,
 * and in case of other signal we return 2. For implementation
 * of these return values see Lib/System.hpp.
 *
 * In case execution was terminated by the timer, return value is 1.
 * (see @c timeLimitReached() in Lib/Timer.cpp)
 */
int g_returnValue = 1;

/**
 * Preprocess input problem
 *
 */
Problem* getPreprocessedProblem()
{
  CALL("getPreprocessedProblem");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  Shell::Preprocess prepro(*env.options);
  //phases for preprocessing are being set inside the preprocess method
  prepro.preprocess(*prb);
  
  // TODO: could this be the right way to freeing the currently leaking classes like Units, Clauses and Inferences?
  // globUnitList = prb->units();

  return prb;
} // getPreprocessedProblem

void explainException(Exception& exception)
{
  env.beginOutput();
  exception.cry(env.out());
  env.endOutput();
} // explainException

void getRandomStrategy()
{
  CALL("getRandomStrategy()");
  // We might have set random_strategy sat
  if(env.options->randomStrategy()==Options::RandomStrategy::OFF){
    env.options->setRandomStrategy(Options::RandomStrategy::ON);
  }

  // One call to randomize before preprocessing (see Options)
  env.options->randomizeStrategy(0); 
  ScopedPtr<Problem> prb(getPreprocessedProblem());
  // Then again when the property is here
  env.options->randomizeStrategy(prb->getProperty()); 

  // It is possible that the random strategy is still incorrect as we don't
  // have access to the Property when setting preprocessing
  env.options->checkProblemOptionConstraints(prb->getProperty());
}

void doProving()
{
  CALL("doProving()");
  // One call to randomize before preprocessing (see Options)
  env.options->randomizeStrategy(0);

  ScopedPtr<Problem> prb(getPreprocessedProblem());

  // Then again when the property is here (this will only randomize non-default things if an option is set to do so)
  env.options->randomizeStrategy(prb->getProperty()); 

  // this will provide warning if options don't make sense for problem
  //env.options->checkProblemOptionConstraints(prb->getProperty()); 

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

  /* CAREFUL: Make sure that the order
   * 1) getProperty, 2) normalise, 3) TheoryFinder::search
   * is the same as in PortfolioMode::searchForProof
   * also, cf. the beginning of Preprocessing::preprocess*/
  Property* property = prb->getProperty();
  Normalisation().normalise(*prb);
  TheoryFinder(prb->units(), property).search();

  env.beginOutput();
  env.out() << property->categoryString() << ' ' << property->props() << ' '
	  << property->atoms() << "\n";
  env.endOutput();

  //we have succeeded with the profile mode, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // profileMode

void outputResult(ostream& out) {
  CALL("outputResult");

  switch(env.statistics->terminationReason) {
  case Statistics::UNKNOWN:
    cout<<"unknown"<<endl;
    break;
  case Statistics::INAPPROPRIATE:
    cout<<"inappropriate"<<endl;
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
  if(env.options->mode()!=Options::Mode::SPIDER){
    env.statistics->print(env.out());
  }
}



void boundPropagationMode(){
#if GNUMP
  CALL("boundPropagationMode::doSolving()");

  //adjust vampire options in order to serve the purpose of bound propagation
  if ( env.options->proof() == env.options->PROOF_ON ) {
    env.options->setProof(env.options->PROOF_OFF);
  }

  //this ensures the fact that int's read in smtlib file are treated as reals
  env.options->setSmtlibConsiderIntsReal(true);

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


  env.beginOutput();
  outputResult(env.out());
  env.endOutput();

  if (env.statistics->terminationReason==Statistics::REFUTATION
      || env.statistics->terminationReason==Statistics::SATISFIABLE) {
    g_returnValue=0;
  }

#endif
}

// prints Unit u at an index to latexOut using the LaTeX object
void outputUnitToLaTeX(LaTeX& latex, ofstream& latexOut, Unit* u,unsigned index)
{
    vstring stringform = latex.toString(u);
    latexOut << index++ << " & ";
    unsigned count = 0;
    for(const char* p = stringform.c_str();*p;p++){
      latexOut << *p;
      count++;
      if(count>80 && *p==' '){
        latexOut << "\\\\ \n & ~~~~~";
        count=0;
      }
    }
    latexOut << "\\\\" << endl;
}

// print the clauses of a problem to a LaTeX file
void outputClausesToLaTeX(Problem* prb)
{
  CALL("outputClausesToLaTeX");
  ASS(env.options->latexOutput()!="off");

  BYPASSING_ALLOCATOR; // not sure why we need this yet, ofstream?

  LaTeX latex;
  ofstream latexOut(env.options->latexOutput().c_str());
  latexOut << latex.header() << endl;
  latexOut << "\\section{Problem "<<env.options->problemName() << "}" << endl;
  //TODO output more header
  latexOut << "\\[\n\\begin{array}{ll}" << endl;

  CompositeISE simplifier;
  simplifier.addFront(new TrivialInequalitiesRemovalISE());
  simplifier.addFront(new TautologyDeletionISE());
  simplifier.addFront(new DuplicateLiteralRemovalISE());

  unsigned index=0;
  ClauseIterator cit = prb->clauseIterator();
  while (cit.hasNext()) {
    Clause* cl = cit.next();
    cl = simplifier.simplify(cl);
    if (!cl) {
      continue;
    }
    outputUnitToLaTeX(latex,latexOut,cl,index++);
  }
  latexOut  << "\\end{array}\n\\]" << latex.footer() << "\n";

  //close ofstream?
}

// print the formulas of a problem to a LaTeX file
void outputProblemToLaTeX(Problem* prb)
{
  CALL("outputProblemToLaTeX");
  ASS(env.options->latexOutput()!="off");

  BYPASSING_ALLOCATOR; // not sure why we need this yet, ofstream?

  LaTeX latex;
  ofstream latexOut(env.options->latexOutput().c_str());
  latexOut << latex.header() << endl;
  latexOut << "\\section{Problem "<<env.options->problemName() << "}" << endl;
  //TODO output more header
  latexOut << "\\[\n\\begin{array}{ll}" << endl;

  //TODO  get symbol and sort declarations into LaTeX
  //UIHelper::outputSortDeclarations(env.out());
  //UIHelper::outputSymbolDeclarations(env.out());

  UnitList::Iterator units(prb->units());

  unsigned index = 0;
  while (units.hasNext()) {
    Unit* u = units.next();
    outputUnitToLaTeX(latex,latexOut,u,index++);
  }
  latexOut  << "\\end{array}\n\\]" << latex.footer() << "\n";

  //close ofstream?
}

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
void preprocessMode(bool theory)
{
  CALL("preprocessMode()");

  Problem* prb = UIHelper::getInputProblem(*env.options);

  TimeCounter tc2(TC_PREPROCESSING);

  // preprocess without clausification
  Shell::Preprocess prepro(*env.options);
  prepro.turnClausifierOff();
  if(env.options->mode() == Options::Mode::PREPROCESS2){
    prepro.keepSimplifyStep();
  }
  prepro.preprocess(*prb);

  env.beginOutput();
  UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());
  while (units.hasNext()) {
    Unit* u = units.next();
    if (!env.options->showFOOL()) {
      if (u->inference()->rule() == Inference::FOOL_AXIOM_TRUE_NEQ_FALSE || u->inference()->rule() == Inference::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE) {
        continue;
      }
    }

    if (theory) {
      Formula* f = u->getFormula();
      FormulaUnit* fu = new FormulaUnit(f,u->inference(),u->inputType() == Unit::CONJECTURE ? Unit::NEGATED_CONJECTURE : u->inputType()); // CONJECTURE is evil, as it cannot occur multiple times
      env.out() << TPTPPrinter::toString(fu) << "\n";
    } else {
      env.out() << TPTPPrinter::toString(u) << "\n";
    }
  }
  env.endOutput();

  if(env.options->latexOutput()!="off"){ outputProblemToLaTeX(prb); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // preprocessMode

/**
 *
 * @author Giles
 * @since 6/10/2015
 */
void modelCheckMode()
{
  CALL("modelCheckMode");

  env.options->setOutputAxiomNames(true);
  Problem* prb = UIHelper::getInputProblem(*env.options);

  FMB::ModelCheck::doCheck(prb);

} // modelCheckMode


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
  UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());
  UnitList::Iterator units(prb->units());

  while (units.hasNext()) {
    Unit* u = units.next();
    env.out() << TPTPPrinter::toString(u) << "\n";
  }
  env.endOutput();

  if(env.options->latexOutput()!="off"){ outputProblemToLaTeX(prb); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // outputMode

static SATClauseList* getInputClauses(const char* fname, unsigned& varCnt)
{
  CALL("getInputClauses");
  TimeCounter tc(TC_PARSING);

  return DIMACS::parse(fname, varCnt);
}

static SATClauseIterator preprocessClauses(SATClauseList* clauses) {
  CALL("preprocessClauses");
  TimeCounter tc(TC_PREPROCESSING);
  
  return SAT::Preprocess::removeDuplicateLiterals(pvi(SATClauseList::DestructiveIterator(clauses)));
}


void satSolverMode()
{
  CALL("satSolverMode()");
  TimeCounter tc(TC_SAT_SOLVER);
  SATSolverSCP solver;
  
  switch(env.options->satSolver()) {
    case Options::SatSolver::VAMPIRE:  
      solver = new TWLSolver(*env.options);
      break;
    case Options::SatSolver::MINISAT:
      solver = new MinisatInterfacingNewSimp(*env.options);
      break;      
    default:
      ASSERTION_VIOLATION(env.options->satSolver());
  }
    
  //get the clauses; 
  SATClauseList* clauses;
  unsigned varCnt=0;

  SATSolver::Status res; 
  
  clauses = getInputClauses(env.options->inputFile().c_str(), varCnt);
  
  solver->ensureVarCount(varCnt);
  solver->addClausesIter(preprocessClauses(clauses));

  res = solver->solve();

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
  if (env.statistics->terminationReason == Statistics::SAT_UNSATISFIABLE
      || env.statistics->terminationReason == Statistics::SAT_SATISFIABLE) {
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
  }

}
void vampireMode()
{
  CALL("vampireMode()");

  if (env.options->mode() == Options::Mode::CONSEQUENCE_ELIMINATION) {
    env.options->setUnusedPredicateDefinitionRemoval(false);
  }

  doProving();

  env.beginOutput();
  UIHelper::outputResult(env.out());
  env.endOutput();

  if (env.statistics->terminationReason == Statistics::REFUTATION
      || env.statistics->terminationReason == Statistics::SATISFIABLE) {
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
  }
} // vampireMode

void spiderMode()
{
  CALL("spiderMode()");
  env.options->setBadOptionChoice(Options::BadOption::HARD);
  env.options->setOutputMode(Options::Output::SPIDER);
  Exception* exception = 0;
#if VZ3
  z3::exception* z3_exception = 0;
#endif
  bool noException = true;
  try {
    doProving();
  } catch (Exception& e) {
    exception = &e;
    noException = false;
#if VZ3
  } catch(z3::exception& e){
    z3_exception = &e; 
    noException = false;
#endif
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
      reportSpiderStatus('t');
    case Statistics::MEMORY_LIMIT:
      reportSpiderStatus('m');
    case Statistics::UNKNOWN:
    case Statistics::INAPPROPRIATE:
      reportSpiderStatus('u');
    case Statistics::REFUTATION_NOT_FOUND:
      if(env.statistics->discardedNonRedundantClauses>0){
        reportSpiderStatus('n');
      }
      else{
        reportSpiderStatus('i');
      }
      break;
    case Statistics::SATISFIABLE:
      reportSpiderStatus('-');
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    default:
      ASSERTION_VIOLATION;
    }
    // env.statistics->print(env.out());
  } else {
#if VZ3
    if(z3_exception){
      if(strcmp(z3_exception->msg(),"out of memory\n")){
        reportSpiderStatus('m');
      }
      else{ reportSpiderFail(); }
    }
    else{
#endif
      reportSpiderFail();
      ASS(exception); 
      explainException(*exception); 
#if VZ3
    }
#endif
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
  }
  env.endOutput();
} // spiderMode

void clausifyMode(bool theory)
{
  CALL("clausifyMode()");

  CompositeISE simplifier;
  simplifier.addFront(new TrivialInequalitiesRemovalISE());
  simplifier.addFront(new TautologyDeletionISE());
  simplifier.addFront(new DuplicateLiteralRemovalISE());

  ScopedPtr<Problem> prb(getPreprocessedProblem());

  env.beginOutput();
  UIHelper::outputSortDeclarations(env.out());
  UIHelper::outputSymbolDeclarations(env.out());

  ClauseIterator cit = prb->clauseIterator();
  bool printed_conjecture = false;
  while (cit.hasNext()) {
    Clause* cl = cit.next();
    cl = simplifier.simplify(cl);
    if (!cl) {
      continue;
    }
    printed_conjecture |= cl->inputType() == Unit::CONJECTURE || cl->inputType() == Unit::NEGATED_CONJECTURE;
    if (theory) {
      Formula* f = Formula::fromClause(cl);
      FormulaUnit* fu = new FormulaUnit(f,cl->inference(),cl->inputType() == Unit::CONJECTURE ? Unit::NEGATED_CONJECTURE : cl->inputType()); // CONJECTURE is evil, as it cannot occur multiple times
      env.out() << TPTPPrinter::toString(fu) << "\n";
    } else {
      env.out() << TPTPPrinter::toString(cl) << "\n";
    }
  }
  if(!printed_conjecture && UIHelper::haveConjecture()){
    unsigned p = env.signature->addFreshPredicate(0,"p");
    Clause* c = new(2) Clause(2,Unit::InputType::NEGATED_CONJECTURE,new Inference0(Inference::INPUT));
    (*c)[0] = Literal::create(p,0,true,false,0);
    (*c)[1] = Literal::create(p,0,false,false,0);
    env.out() << TPTPPrinter::toString(c) << "\n";
  }
  env.endOutput();

  if (env.options->latexOutput() != "off") { outputClausesToLaTeX(prb.ptr()); }

  //we have successfully output all clauses, so we'll terminate with zero return value
  vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
} // clausifyMode

void axiomSelectionMode()
{
  CALL("axiomSelectionMode()");

  env.options->setSineSelection(Options::SineSelection::AXIOMS);

  ScopedPtr<Problem> prb(UIHelper::getInputProblem(*env.options));

  if (prb->hasFOOL()) {
    FOOLElimination().apply(*prb);
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

    Shell::Preprocess prepro(*env.options);
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

  } catch (MemoryLimitExceededException&) {
    env.beginOutput();
    env.out() << "Memory limit exceeded\n";
    env.endOutput();
  } catch (TimeLimitExceededException&) {
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


  System::registerArgv0(argv[0]);
  System::setSignalHandlers();
  // create random seed for the random number generation
  Lib::Random::setSeed(123456);

  START_CHECKING_FOR_ALLOCATOR_BYPASSES;

  try {
    // read the command line and interpret it
    Shell::CommandLine cl(argc, argv);
    cl.interpret(*env.options);

    // If any of these options are set then we just need to output and exit
    if (env.options->showHelp() ||
        env.options->showOptions() ||
        env.options->showExperimentalOptions() ||
        !env.options->explainOption().empty() ||
        env.options->printAllTheoryAxioms()) {
      env.beginOutput();
      env.options->output(env.out());
      env.endOutput();
      exit(0);
    }

    Allocator::setMemoryLimit(env.options->memoryLimit() * 1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::Mode::AXIOM_SELECTION:
      axiomSelectionMode();
      break;
    case Options::Mode::GROUNDING:
      groundingMode();
      break;
/*
    case Options::Mode::BOUND_PROP:
#if GNUMP
     boundPropagationMode();
#else
     NOT_IMPLEMENTED;
#endif
      break;
*/
    case Options::Mode::SPIDER:
      spiderMode();
      break;
    case Options::Mode::RANDOM_STRATEGY:
      getRandomStrategy();
      break;
    case Options::Mode::CONSEQUENCE_ELIMINATION:
    case Options::Mode::VAMPIRE:
      vampireMode();
      break;

    case Options::Mode::CASC:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);
      env.options->setSchedule(Options::Schedule::CASC);
      env.options->setOutputMode(Options::Output::SZS);
      env.options->setProof(Options::Proof::TPTP);
      env.options->setOutputAxiomNames(true);
      //env.options->setTimeLimitInSeconds(300);
      env.options->setMemoryLimit(128000);

      if (CASC::PortfolioMode::perform(1.30)) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::CASC_SAT:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);
      env.options->setSchedule(Options::Schedule::CASC_SAT);
      env.options->setOutputMode(Options::Output::SZS);
      env.options->setProof(Options::Proof::TPTP);
      env.options->setOutputAxiomNames(true);
      //env.options->setTimeLimitInSeconds(300);
      env.options->setMemoryLimit(128000);

      if (CASC::PortfolioMode::perform(1.30)) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::SMTCOMP:
      env.options->setIgnoreMissing(Options::IgnoreMissing::OFF);
      env.options->setInputSyntax(Options::InputSyntax::SMTLIB2);
      env.options->setOutputMode(Options::Output::SMTCOMP);
      env.options->setSchedule(Options::Schedule::SMTCOMP);
      env.options->setProof(Options::Proof::OFF);
      env.options->setMulticore(0); // use all available cores
      env.options->setTimeLimitInSeconds(1800);
      env.options->setMemoryLimit(128000);
      env.options->setStatistics(Options::Statistics::NONE);

      //TODO needed?
      // to prevent from terminating by time limit
      env.options->setTimeLimitInSeconds(100000);

      if (CASC::PortfolioMode::perform(1.3)){
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      else {
        cout << "unknown" << endl;
      }
      break;

    case Options::Mode::PORTFOLIO:
      env.options->setIgnoreMissing(Options::IgnoreMissing::WARN);

      if (CASC::PortfolioMode::perform(1.0)) {
        vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      }
      break;

    case Options::Mode::CASC_LTB: {
      bool learning = env.options->ltbLearning()!=Options::LTBLearning::OFF;
      try {
        if(learning){
          CASC::CLTBModeLearning::perform();
        }
        else{
          CASC::CLTBMode::perform();
        }
      } catch (Lib::SystemFailException& ex) {
        cerr << "Process " << getpid() << " received SystemFailException" << endl;
        ex.cry(cerr);
        cerr << " and will now die" << endl;
      }
      //we have processed the ltb batch file, so we can return zero
      vampireReturnValue = VAMP_RESULT_STATUS_SUCCESS;
      break;
    }
    case Options::Mode::MODEL_CHECK:
      modelCheckMode();
      break;

    case Options::Mode::CLAUSIFY:
      clausifyMode(false);
      break;

    case Options::Mode::TCLAUSIFY:
      clausifyMode(true);
      break;

    case Options::Mode::OUTPUT:
      outputMode();
      break;

    case Options::Mode::PROFILE:
      profileMode();
      break;

    case Options::Mode::PREPROCESS:
    case Options::Mode::PREPROCESS2:
      preprocessMode(false);
      break;

    case Options::Mode::TPREPROCESS:
      preprocessMode(true);
      break;

    case Options::Mode::SAT:
      satSolverMode();
      break;

    default:
      USER_ERROR("Unsupported mode");
    }
#if CHECK_LEAKS
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
#if VZ3
  catch(z3::exception& exception){
    BYPASSING_ALLOCATOR;
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    cout << "Z3 exception:\n" << exception.msg() << endl;
    reportSpiderFail();
  }
#endif
  catch (UserErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  } 
catch (Parse::TPTP::ParseErrorException& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    explainException(exception);
  }
  catch (Exception& exception) {
    vampireReturnValue = VAMP_RESULT_STATUS_UNHANDLED_EXCEPTION;
    reportSpiderFail();
#if CHECK_LEAKS
    MemoryLeak::cancelReport();
#endif
    env.beginOutput();
    explainException(exception);
    //env.statistics->print(env.out());
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

