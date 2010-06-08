/**
 * @file InputReader.cpp
 * Implements class InputReader.
 */

#include <string>
#include <fstream>

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/InferenceStore.hpp"

#include "Interpolants.hpp"
#include "LaTeX.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "TPTPLexer.hpp"
#include "TPTPParser.hpp"

#include "UIHelper.hpp"

namespace Shell
{

using namespace Lib;
using namespace Kernel;

bool UIHelper::cascMode=false;
bool UIHelper::s_haveConjecture=false;

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
 * Output result based on the content of
 * @b env.statistics->terminationReason
 *
 * If LaTeX output is enabled, it is output in this function.
 *
 * If interpolant output is enabled, it is output in this function.
 */
void UIHelper::outputResult()
{
  CALL("UIHelper::outputResult");

  switch (env.statistics->terminationReason) {
  case Statistics::REFUTATION:
    env.out << "Refutation found. Thanks to "
	      << env.options->thanks() << "!\n";
    if(cascMode) {
      env.out<<"% SZS status "<<( UIHelper::haveConjecture() ? "Theorem" : "Unsatisfiable" )
	  <<" for "<<env.options->problemName()<<endl;
    }
    if (env.options->proof() != Options::PROOF_OFF) {
//	Shell::Refutation refutation(env.statistics->refutation,
//		env.options->proof() == Options::PROOF_ON);
//	refutation.output(env.out);
      if(cascMode) {
	env.out<<"% SZS output start Proof for "<<env.options->problemName()<<endl;
      }
      InferenceStore::instance()->outputProof(env.out, env.statistics->refutation);
      if(cascMode) {
	env.out<<"% SZS output end Proof for "<<env.options->problemName()<<endl;
      }
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
    if(cascMode) {
      env.out << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
	  <<" for "<<env.options->problemName()<<endl;
    }
    break;
  case Statistics::UNKNOWN:
    env.out << "Unknown reason of termination!\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  env.statistics->print();
}


}
