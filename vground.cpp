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
#include "Lib/MapToLIFO.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Indexing/TermSharing.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Indexing/LiteralMiniIndex.hpp"

#include "Shell/CommandLine.hpp"
#include "Shell/GeneralSplitting.hpp"
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

void groundingMode()
{
  CALL("groundingMode()");

  try {
    Property property;

    env.signature = new Kernel::Signature;
    UnitList* units;
    {
      string inputFile = env.options->inputFile();
      ifstream input(inputFile.c_str());
      TPTPLexer lexer(input);
      TPTPParser parser(lexer);
      units = parser.units();
    }

    property.scan(units);

    Preprocess prepro(property,*env.options);
    prepro.preprocess(units);

    Property newProperty;
    newProperty.scan(units);

    globUnitList=units;

    ClauseIterator clauses=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );


    if(newProperty.equalityAtoms()) {
      ClauseList* eqAxioms=Grounding::getEqualityAxioms(newProperty.positiveEqualityAtoms()!=0);
      clauses=pvi( getConcatenatedIterator(ClauseList::DestructiveIterator(eqAxioms), clauses) );
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
    DIMACS::outputGroundedProblem(insts, nameCtx, env.out);

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

    if(options.mode()!=Options::MODE_GROUNDING) {
      USER_ERROR("Invalid mode: must be \"grouding\"");
    }

    groundingMode();

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

  return EXIT_SUCCESS;
} // main

