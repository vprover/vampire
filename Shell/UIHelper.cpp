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
#include "Kernel/Problem.hpp"

#include "Parse/SMTLIB.hpp"
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

bool UIHelper::unitSpecNumberComparator(UnitSpec us1, UnitSpec us2)
{
  CALL("unitSpecNumberComparator");

  return us1.unit()->number() < us2.unit()->number();
}

void UIHelper::outputAllPremises(ostream& out, UnitList* units, string prefix)
{
  CALL("UIHelper::outputAllPremises");

#if 1
  InferenceStore::instance()->outputProof(cerr, units);
#else
  Stack<UnitSpec> prems;
  Stack<UnitSpec> toDo;
  DHSet<UnitSpec> seen;

  //get the units to start with
  UnitList::Iterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    toDo.push(UnitSpec(u));
  }

  while(toDo.isNonEmpty()) {
    UnitSpec us = toDo.pop();
    UnitSpecIterator pars = InferenceStore::instance()->getParents(us);
    while(pars.hasNext()) {
      UnitSpec par = pars.next();
      if(seen.contains(par)) {
	continue;
      }
      prems.push(par);
      toDo.push(par);
      seen.insert(par);
    }
  }

  std::sort(prems.begin(), prems.end(), UIHelper::unitSpecNumberComparator);

  Stack<UnitSpec>::BottomFirstIterator premIt(prems);
  while(premIt.hasNext()) {
    UnitSpec prem = premIt.next();
    out << prefix << prem.toString() << endl;
  }
#endif
}

void UIHelper::outputSaturatedSet(ostream& out, UnitIterator uit)
{
  CALL("UIHelper::outputSaturatedSet");

  out<<"# SZS output start Saturation."<<endl;

  while(uit.hasNext()) {
    Unit* cl = uit.next();
    out << TPTP::toString(cl) << endl;
  }

  out<<"# SZS output end Saturation."<<endl;
}

/**
 * Return problem object with units obtained according to the content of
 * @b env.options
 *
 * No preprocessing is performed on the units.
 */
Problem* UIHelper::getInputProblem(const Options& opts)
{
  CALL("UIHelper::getInputProblem");

  TimeCounter tc1(TC_PARSING);
  env.statistics->phase=Statistics::PARSING;


  string inputFile = opts.inputFile();

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
  switch (opts.inputSyntax()) {
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
  case Options::IS_SMTLIB:
  {
    Parse::SMTLIB parser(opts);
    parser.parse(*input);
    units = parser.getFormulas();
    s_haveConjecture=true;
  }
  break;
  }

  if(inputFile!="") {
    delete static_cast<ifstream*>(input);
    input=0;
  }

  Problem* res = new Problem(units);

  env.statistics->phase=Statistics::UNKNOWN_PHASE;
  return res;
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
    if(env.statistics->discardedNonRedundantClauses) {
      out << "Refutation not found, non-redundant clauses discarded\n";
    } else {
      out << "Refutation not found, incomplete strategy\n";
    }
    break;
  case Statistics::SATISFIABLE:
    outputSatisfiableResult(out);
    break;
  case Statistics::UNKNOWN:
    out << "Unknown reason of termination!\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  env.statistics->print(out);
}

void UIHelper::outputSatisfiableResult(ostream& out)
{
  CALL("UIHelper::outputSatisfiableResult");

  out << "Satisfiable!\n";
#if SATISFIABLE_IS_SUCCESS
  if(cascMode && !satisfiableStatusWasAlreadyOutput) {
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
  else if(env.statistics->saturatedSet) {
    outputSaturatedSet(out, pvi(UnitList::Iterator(env.statistics->saturatedSet)));
  }
#endif
}

void UIHelper::outputIntroducedSymbolDeclarations(ostream& out)
{
  CALL("UIHelper::outputIntroducedSymbolDeclarations");

  Signature& sig = *env.signature;

  unsigned funcs = sig.functions();
  for(unsigned i=0; i<funcs; ++i) {
    if(!sig.getFunction(i)->introduced()) {
      continue;
    }
    outputSymbolTypeDeclarationIfNeeded(out, true, i);
  }
  unsigned preds = sig.predicates();
  for(unsigned i=0; i<preds; ++i) {
    if(!sig.getPredicate(i)->introduced()) {
      continue;
    }
    outputSymbolTypeDeclarationIfNeeded(out, false, i);
  }
}

void UIHelper::outputSymbolTypeDeclarationIfNeeded(ostream& out, bool function, unsigned symNumber)
{
  CALL("UIHelper::outputSymbolTypeDeclarationIfNeeded");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);

  if(sym->interpreted()) {
    //there is no need to output type definitions for interpreted symbols
    return;
  }

  BaseType* type = function ? static_cast<BaseType*>(sym->fnType()) : sym->predType();

  if(type->isAllDefault()) {
    return;
  }

  out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ",type, "
      << sym->name() << ": ";

  unsigned arity = sym->arity();
  if(arity>0) {
    if(arity==1) {
      out << env.sorts->sortName(type->arg(0));
    }
    else {
      out << "(";
      for(unsigned i=0; i<arity; i++) {
	if(i>0) {
	  out << " * ";
	}
	out << env.sorts->sortName(type->arg(i));
      }
      out << ")";
    }
    out << " > ";
  }
  if(function) {
    out << env.sorts->sortName(sym->fnType()->result());
  }
  else {
    out << "$o";
  }
  out << " )." << endl;
}

}
