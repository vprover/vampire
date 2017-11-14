
/*
 * File vltb.cpp.
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

#include "Debug/Tracer.hpp"

#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
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

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Term.hpp"

#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/LiteralMiniIndex.hpp"

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
#include "Shell/TPTP.hpp"

#include "Shell/LTB/Builder.hpp"
#include "Shell/LTB/Selector.hpp"

#include "Parse/TPTP.hpp"

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

ClauseIterator getProblemClauses()
{
  CALL("getProblemClauses");

  Shell::LTB::Selector selector;
  Property property;

  UnitList* units;
  {
    TimeCounter tc1(TC_PARSING);

    vstring inputFile = env.options->inputFile();

    istream* input;
    if(inputFile=="") {
      input=&cin;
    } else {
      input=new ifstream(inputFile.c_str());
      if(input->fail()) {
        USER_ERROR("Cannot open input file: "+inputFile);
      }
    }

    env.statistics->phase=Statistics::PARSING;
    if(env.options->inputSyntax()!=Options::IS_TPTP) {
      USER_ERROR("Unsupported input syntax");
    }

    {
      Parse::TPTP parser(*input);
      StringList::Iterator names(selector.theoryFileNames());
      while (names.hasNext()) {
	parser.addForbiddenInclude(names.next());
      }
      parser.parse()
      units = parser.units();
    }

    if(inputFile!="") {
      delete static_cast<ifstream*>(input);
      input=0;
    }
  }

  selector.selectForProblem(units);

  TimeCounter tc2(TC_PREPROCESSING);

  env.statistics->phase=Statistics::PROPERTY_SCANNING;
  property.scan(units);
  Preprocess prepro(property,*env.options);
  //phases for preprocessing are being set inside the proprocess method
  prepro.preprocess(units);

  globUnitList=units;

  return pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );
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
    if(env.options->showInterpolant()!=Options::INTERP_OFF) {
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

void explainException (Exception& exception)
{
  exception.cry(env.out);
} // explainException

void ltbBuildMode()
{
  CALL("ltbBuildMode");

  vstring inputFile = env.options->inputFile();

  istream* input0;
  if(inputFile=="") {
    input0=&cin;
  } else {
    input0=new ifstream(inputFile.c_str());
    if(input0->fail()) {
      USER_ERROR("Cannot open input file: "+inputFile);
    }
  }
  istream& input=*input0;

  Stack<vstring> nameStack;
  char lineBuf[1024];

  while(!input.eof()) {
    input.getline(lineBuf, 1024);
    vstring line(lineBuf);
    if(line.length()<12 || line.substr(0,9)!="include('" || line.substr(line.length()-3,3)!="').") {
      continue;
    }
    vstring fname(line, 9, line.length()-3-9);

    nameStack.push(fname);
  }

  Shell::LTB::Builder builder;
  builder.build(pvi( Stack<vstring>::Iterator(nameStack) ));

  if(inputFile!="") {
    delete static_cast<ifstream*>(&input);
  }
}

void ltbSolveMode()
{
  CALL("ltbSolveMode");

  env.beginOutput();
  env.out()<<env.options->testId()<<" on "<<env.options->problemName()<<endl;
  env.endOutput();
  try {
    ClauseIterator clauses=getProblemClauses();
    Unit::onPreprocessingEnd();

    env.statistics->phase=Statistics::SATURATION;
    MainLoopSP salg=MainLoop::createFromOptions();
    salg->addInputClauses(clauses);

    MainLoopResult sres(salg->saturate());
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
  outputResult();
}

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
    Shell::CommandLine cl(argc,argv);
    cl.interpret(*env.options);

    Allocator::setMemoryLimit(env.options->memoryLimit()*1048576ul);
    Lib::Random::setSeed(env.options->randomSeed());

    switch (env.options->mode())
    {
    case Options::MODE_LTB_BUILD:
      ltbBuildMode();
      break;
    case Options::MODE_LTB_SOLVE:
      ltbSolveMode();
      break;
    default:
      USER_ERROR("Specified mode is not supported by the vltb executable (use '--mode ltb_build' or '--mode ltb_solve')");
      break;
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

