/**
 * @file InputReader.cpp
 * Implements class InputReader.
 */

#include <string>
#include <fstream>

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/InferenceStore.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Interpolants.hpp"
#include "LaTeX.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "Preprocess.hpp"
#include "Property.hpp"
#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "TPTPLexer.hpp"
#include "TPTPParser.hpp"

#include "UIHelper.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;

bool UIHelper::s_haveConjecture=false;

/**
 * Return list of input units obtained according to the content of
 * @b env.options
 *
 * No preprocessing is performed on the units.
 */
UnitList* UIHelper::getInputUnits()
{
  CALL("UIHelper::getUnits");

  TimeCounter tc1(TC_PARSING);
  env.statistics->phase=Statistics::PARSING;


  string inputFile = env.options->inputFile();

  istream* input;
  if(inputFile=="") {
    input=&cin;
  } else {
    input=new ifstream(inputFile.c_str());
  }


  UnitList* units;
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
    s_haveConjecture=parser.haveConjecture();
  }
  break;
  }

  if(inputFile!="") {
    delete static_cast<ifstream*>(input);
    input=0;
  }

  env.statistics->phase=Statistics::UNKNOWN_PHASE;
  return units;
}

/**
 * Run the Vampire saturation loop (based on the content of @b env.options )
 * on @b clauses
 *
 * The result of the loop is in @b env.statistics
 *
 * The content of the @b units list after return from the function is
 * undefined
 *
 * The function does not necessarily return (e.g. in the case of timeout,
 * the process is aborted)
 */
void UIHelper::runVampireSaturation(ClauseIterator clauses)
{
  try {
    runVampireSaturationImpl(clauses);
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

/**
 * Run the Vampire preprocessing and saturation loop (based on the content
 * of @b env.options ) on @b units. If @b prop is nonzero, do not scan
 * properties of the units, but use @b prop as a property object instead.
 *
 * The result of the loop is in @b env.statistics
 *
 * The content of the @b units list after return from the function is
 * undefined
 *
 * The function does not necessarily return (e.g. in the case of timeout,
 * the process is aborted)
 */
void UIHelper::runVampire(UnitList* units, Property* prop)
{
  CALL("UIHelper::runVampire");

  try
  {
    ClauseIterator clauses;
    {
      TimeCounter tc2(TC_PREPROCESSING);

      Property prop1;
      if(prop==0) {
	env.statistics->phase=Statistics::PROPERTY_SCANNING;
	prop1.scan(units);

	prop=&prop1;
      }

      Preprocess prepro(*prop,*env.options);
      //phases for preprocessing are being set inside the proprocess method
      prepro.preprocess(units);

      clauses=pvi( getStaticCastIterator<Clause*>(UnitList::Iterator(units)) );
    }
    runVampireSaturationImpl(clauses);
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

/**
 * Private version of the @b runVampireSaturation function
 * that is not protected for resource-limit exceptions
 */
void UIHelper::runVampireSaturationImpl(ClauseIterator clauses)
{
  Unit::onPreprocessingEnd();
  env.statistics->phase=Statistics::SATURATION;
  SaturationAlgorithmSP salg=SaturationAlgorithm::createFromOptions();
  salg->addInputClauses(clauses);

  SaturationResult sres(salg->saturate());
  env.statistics->phase=Statistics::FINALIZATION;
  Timer::setTimeLimitEnforcement(false);
  sres.updateStatistics();
}

/**
 * Output result based on the content of
 * @b env.statistics->terminationReason
 *
 * If LaTeX output is enabled, it is output in this function.
 *
 * If interpolant output is enabled, it is output in this function.
 */
void UIHelper::outputResult(ostream& out)
{
  CALL("UIHelper::outputResult");

  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    out << "Refutation found. Thanks to "
	      << env.options->thanks() << "!\n";
    if(cascMode) {
      out<<"% SZS status "<<( UIHelper::haveConjecture() ? "Theorem" : "Unsatisfiable" )
	  <<" for "<<env.options->problemName()<<endl;
    }
    if (env.options->proof() != Options::PROOF_OFF) {
//	Shell::Refutation refutation(env.statistics->refutation,
//		env.options->proof() == Options::PROOF_ON);
//	refutation.output(out);
      if(cascMode) {
	out<<"% SZS output start Proof for "<<env.options->problemName()<<endl;
      }
      InferenceStore::instance()->outputProof(out, env.statistics->refutation);
      if(cascMode) {
	out<<"% SZS output end Proof for "<<env.options->problemName()<<endl;
      }
    }
    if(env.options->showInterpolant()) {
      ASS(env.statistics->refutation->isClause());
      Formula* interpolant=Interpolants::getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      out << "Interpolant: " << interpolant->toString() << endl;
    }
    if(env.options->latexOutput()!="off") {
      ofstream latexOut(env.options->latexOutput().c_str());

      LaTeX formatter;
      latexOut<<formatter.refutationToString(env.statistics->refutation);
    }
    break;
  case Statistics::TIME_LIMIT:
    out << "Time limit reached!\n";
    break;
  case Statistics::MEMORY_LIMIT:
#if VDEBUG
    Allocator::reportUsageByClasses();
#endif
    out << "Memory limit exceeded!\n";
    break;
  case Statistics::REFUTATION_NOT_FOUND:
    if(env.options->complete()) {
      ASS_EQ(env.options->saturationAlgorithm(), Options::LRS);
      out << "Refutation not found, LRS age and weight limit was active for some time!\n";
    } else {
      out << "Refutation not found with incomplete strategy!\n";
    }
    break;
  case Statistics::SATISFIABLE:
    out << "Refutation not found!\n";
//    if(cascMode) {
//      out << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
//	  <<" for "<<env.options->problemName()<<endl;
//    }
    break;
  case Statistics::UNKNOWN:
    out << "Unknown reason of termination!\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  env.statistics->print(out);
}


}
