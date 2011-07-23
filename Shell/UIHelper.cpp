/**
 * @file UIHelper.cpp
 * Implements class UIHelper.
 */

#include <string>
#include <fstream>

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/InferenceStore.hpp"

#include "Parse/TPTP.hpp"

#include "AnswerExtractor.hpp"
#include "InterpolantMinimizer.hpp"
#include "Interpolants.hpp"
#include "LaTeX.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "TPTP.hpp"
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
    if(input->fail()) {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
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
    Parse::TPTP parser(*input);
    parser.parse();
    units = parser.units();
    s_haveConjecture=parser.containsConjecture();
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
    if(env.options->questionAnswering()!=Options::QA_OFF) {
      ASS(env.statistics->refutation->isClause());
      AnswerExtractor::tryOutputAnswer(static_cast<Clause*>(env.statistics->refutation));
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
	out<<"% SZS output end Proof for "<<env.options->problemName()<<endl<<flush;
      }
    }
    if(env.options->showInterpolant()==Options::INTERP_ON) {
      ASS(env.statistics->refutation->isClause());
      Formula* interpolant=Interpolants().getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      out << "Interpolant: " << interpolant->toString() << endl;
    }
    if(env.options->showInterpolant()==Options::INTERP_MINIMIZED) {
      ASS(env.statistics->refutation->isClause());
//      {
//	Formula* oldInterpolant=Interpolants().getInterpolant(static_cast<Clause*>(env.statistics->refutation));
//      }
//      Formula* interpolant=InterpolantMinimizer().getInterpolant(static_cast<Clause*>(env.statistics->refutation));
//      out << "Interpolant: " << interpolant->toString() << endl;

      Formula* oldInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, true, true, "Original interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      Formula* interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, true, true, "Original interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      Formula* cntInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, false, true, "Minimized interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      Formula* quantInterpolant =  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, false, true, "Minimized interpolant quantifiers").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
      out << "Old interpolant: " << TPTP::toString(oldInterpolant) << endl;
      out << "Interpolant: " << TPTP::toString(interpolant) << endl;
      out << "Count minimized interpolant: " << TPTP::toString(cntInterpolant) << endl;
      out << "Quantifiers minimized interpolant: " << TPTP::toString(quantInterpolant) << endl;
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
    if(env.options->complete(*env.property)) {
      ASS_EQ(env.options->saturationAlgorithm(), Options::LRS);
      out << "Refutation not found, LRS age and weight limit was active for some time!\n";
    } else {
      out << "Refutation not found with incomplete strategy!\n";
    }
    break;
  case Statistics::SATISFIABLE:
    out << "Refutation not found!\n";
#if SATISFIABLE_IS_SUCCESS
    if(cascMode) {
      out << "% SZS status "<<( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
	  <<" for "<<env.options->problemName()<<endl;
    }
    if(!env.statistics->model.empty()) {
      if(cascMode) {
	out<<"% SZS output start FiniteModel for "<<env.options->problemName()<<endl;
      }
      out << env.statistics->model;
      if(cascMode) {
	out<<"% SZS output end FiniteModel for "<<env.options->problemName()<<endl;
      }
    }
#endif
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
