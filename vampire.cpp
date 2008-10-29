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
#include "Shell/TheoryFinder.hpp"

#include "Rule/CASC.hpp"
#include "Rule/Prolog.hpp"
#include "Rule/Index.hpp"
#include "Rule/ProofAttempt.hpp"

#if CHECK_LEAKS
#include "Lib/MemoryLeak.hpp"
#endif

#define SPIDER 1
#define SAVE_SPIDER_PROPERTIES 1

using namespace Shell;

// /**
//  * Global function used as runtime error hook for the kernel.
//  */
// void runtimeErrorHook ()
// {
//   CALL("runtimeErrorHook");

//   if (VampireKernel::currentSession()) {
//     cout << "% Trying to shut down current kernel session...\n";
//     VampireKernel::currentSession()->reportError();
//   }

//   XMLElement err("error",
// 		   "some module detected inconsistency in run time");
//   err.addAttribute("type","runtime");
//   Run::currentRun()->addToLog(err);
//   Run::currentRun()->saveLog();
// } // void runtimeErrorHook()

string signalToString (int sigNum)
{
  switch (sigNum)
    {
    case SIGTERM:
      return "SIGTERM";
# ifndef _MSC_VER
    case SIGQUIT:
      return "SIGQUIT";
    case SIGHUP:
      return "SIGHUP";
    case SIGXCPU:
      return "SIGXCPU";
    case SIGBUS:
      return "SIGBUS";
    case SIGTRAP:
      return "SIGTRAP";
# endif
    case SIGINT:
      return "SIGINT";
    case SIGILL:
      return "SIGILL";
    case SIGFPE:
      return "SIGFPE";
    case SIGSEGV:
      return "SIGSEGV";
    case SIGABRT:
      return "SIGABRT";
    default:
      return "UNKNOWN SIGNAL";
    }
} // signalToString

/**
 * Run the Vampire mode: read a problem and try to prove it.
 */
void vampireMode()
{
  CALL("vampireMode()");

  env.signature = new Kernel::Signature;
  string inputFile = env.options->inputFile();
  ifstream input(inputFile.c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Indexing::SubstitutionTree stree(2*env.signature->predicates());

  UnitList::Iterator uit(units);
  cout << "Inserting...\n";
  while (uit.hasNext()) {
    Clause* cls = static_cast<Clause*>(uit.next());
    for (int i = cls->length() - 1;i >= 0;i--) {
      Literal* lit = (*cls)[i];
      stree.insert(lit->header(),lit->args(),cls);
    }
  }
  cout << "Inserting finished!\n";

  UnitList::Iterator dit(units);
  cout << "Deleting...\n";
  while (dit.hasNext()) {
    Clause* cls = static_cast<Clause*>(dit.next());
    for (int i = cls->length() - 1;i >= 0;i--) {
      Literal* lit = (*cls)[i];
      stree.remove(lit->header(),lit->args(),cls);
    }
  }
  cout << "Deleting finished!\n";

  // finding the properties
  Property property;
  property.scan(units);
#if SAVE_SPIDER_PROPERTIES
  TheoryFinder tf(units,&property);
  tf.search();
  cout << property.toSpider(inputFile) << "\n";
  exit(0);
#endif

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

  // added for CASC 2008
//   UnitList::Iterator it(units);
//   Property pp;
//   pp.scan(units);

  

//   cout << pp.toString() << "\n";
//   Rule::Profile pf;
//   pf.scan(units);
//   cout << pf.toString() << "\n";
//   while (it.hasNext()) {
//     Unit* u = it.next();
// //     cout << u->toString() << "\n";
//   }

  // commented out from here on before CASC 2008
//   Resolution::ProofAttempt pa;
//   UnitList::Iterator it(units);
//   while (it.hasNext()) {
//     Unit* u = it.next();
//     ASS(u->isClause());
//     pa.initialClause(static_cast<Clause*>(u));
//   }
//   pa.saturate();

// #if SPIDER
//   switch (env.statistics->terminationReason) {
//   case Statistics::REFUTATION:
//     env.out << "+ ";
//     break;
//   case Statistics::TIME_LIMIT:
//     env.out << "? ";
//     break;
//   default:
//     env.out << "? ";
//     break;
//   }

//   env.out << env.options->problemName() << ' '
// 	  << env.timer->elapsedDeciseconds() << ' ' 
// 	  << env.options->testId() << '\n';

// # else
//   switch (env.statistics->terminationReason) {
//   case Statistics::REFUTATION:
//     env.out << "Refutation found. Thanks to Tanya!\n";
//     if (env.options->proof() != Options::PROOF_OFF) {
//       Shell::Refutation refutation(env.statistics->refutation,
// 				   env.options->proof() == Options::PROOF_ON);
//       refutation.output(env.out);
//     }
//     return;
//   case Statistics::TIME_LIMIT:
//     env.out << "Time limit reached!\n";
//     return;
//   default:
//     env.out << "Refutation not found!\n";
//     return;
//   }
// #endif

#if CHECK_LEAKS
  delete env.signature;
  env.signature = 0;
  MemoryLeak leak;
  leak.release(units);
#endif
} // vampireMode

/**
 * Read a problem and output profiling information about it.
 * @since 03/08/2008 Torrevieja
 */
void profileMode()
{
  CALL("profileMode()");

  env.signature = new Kernel::Signature;
  string inputFile = env.options->inputFile();
  ifstream input(inputFile.c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  // finding the properties
  Property property;
  property.scan(units);
  TheoryFinder tf(units,&property);
  tf.search();
  cout << property.categoryString() << ' '
       << property.props() << ' '
       << property.atoms() << "\n";
} // profileMode

/**
 * Run the Vampire mode: read a problem and try to prove it.
 */
void ruleMode()
{
  CALL("ruleMode()");

  env.signature = new Kernel::Signature;
  ifstream input(env.options->inputFile().c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Property property;
  property.scan(units);

  Preprocess prepro(property,*env.options);
  prepro.preprocess(units);

//   ofstream prologOutput("out.pl");
  Rule::CASC casc(cout);
//   UnitList::Iterator it(units);
  casc.scan(units);
//   Rule::Index index(env.signature);
//   UnitList::Iterator uit(units);
//   Stack<Unit*> goals(7);
//   index.compile(units,goals);
//   Rule::Prolog prolog(prologOutput);
//   prolog.write(index);

#if CHECK_LEAKS
  delete env.signature;
  env.signature = 0;
  MemoryLeak leak;
  leak.release(units);
#endif
} // ruleMode

/**
 * Run the Output mode: read a problem and write relevant clauses only.
 */
void outputMode()
{
  CALL("outputMode()");

  env.signature = new Kernel::Signature;
  ifstream input(env.options->inputFile().c_str());
  TPTPLexer lexer(input);
  TPTPParser parser(lexer);
  UnitList* units = parser.units();

  Set<int,Hash> numbers;
  string proof = env.options->logFile();
  for (;;) {
    unsigned pos = proof.find(',');
    if (pos == string::npos) {
      int i;
      Int::stringToInt(proof,i);
      if (i != -1) {
	numbers.insert(i);
      }
      break;
    }
    else {
      string n = proof.substr(0,pos);
      int i;
      Int::stringToInt(n,i);
      if (i != -1) {
	numbers.insert(i);
      }
      proof = proof.substr(pos+1);
    }
  }

  UnitList::Iterator lit(units);
  while (lit.hasNext()) {
    Unit* u = lit.next();
    if (numbers.contains(u->number())) {
      cout << TPTP::toString(u) << "\n";
    }
  }
} // outputMode

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
 * Signal handling function. Rewritten from the kernel standalone.
 *
 * @param sigNum signal number
 * @since 28/06/2003 Manchester, statistics result registration added
 */
void handleSignal (int sigNum)
{
  // true if a terminal signal has been handled already.
  // to avoid catching signals over and over again
  static bool handled = false;
  string signalDescription = signalToString(sigNum);

  switch (sigNum)
    {
    case SIGTERM:
# ifndef _MSC_VER
    case SIGQUIT:
    case SIGHUP:
    case SIGXCPU:
      if (handled) {
	exit(0);
      }
      handled = true;
      cout << "Aborted by signal " << signalDescription << "\n";
      return;
# endif

    case SIGINT:
      exit(0);
      return;      

    case SIGILL:
    case SIGFPE:
    case SIGSEGV:

# ifndef _MSC_VER
    case SIGBUS:
    case SIGTRAP:
# endif
    case SIGABRT: 
      {
	if (handled) {
	  exit(0);
	}
	handled = true;
	cout << "Aborted by signal " << signalDescription << "\n";
#if VDEBUG
	Debug::Tracer::printStack(cout);
#endif
	exit(0);
	return;
      }

    default:
      break;
    }
} // handleSignal

void setSignalHandlers()
{
  signal(SIGTERM,handleSignal);
  signal(SIGINT,handleSignal);
  signal(SIGILL,handleSignal);
  signal(SIGFPE,handleSignal);
  signal(SIGSEGV,handleSignal);
  signal(SIGABRT,handleSignal);

#ifndef _MSC_VER
  signal(SIGQUIT,handleSignal);
  signal(SIGHUP,handleSignal);
  signal(SIGXCPU,handleSignal);
  signal(SIGBUS,handleSignal);
  signal(SIGTRAP,handleSignal);
#endif
} // void setSignalHandlers()

typedef Lib::Vector<int> Vect;

/**
 * The main function.
  * @since 03/12/2003 many changes related to logging 
  *        and exception handling.
  * @since 10/09/2004, Manchester changed to use knowledge bases
  */
extern void testAllocator();
int main(int argc, char* argv [])
{
  CALL ("main");

  setSignalHandlers();
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
  	return EXIT_SUCCESS;
      case Options::MODE_PROFILE:
	profileMode();
  	return EXIT_SUCCESS;
      case Options::MODE_OUTPUT:
	outputMode();
  	return EXIT_SUCCESS;
      case Options::MODE_RULE:
	ruleMode();
  	return EXIT_SUCCESS;
#if VDEBUG
      default:
  	ASSERTION_VIOLATION;
#endif
      }
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

