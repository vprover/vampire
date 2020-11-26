/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file UIHelper.cpp
 * Implements class UIHelper.
 */

#include <fstream>

#include <cstdlib>
#include <sys/types.h>
#include <unistd.h>
#include <iostream>

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/VString.hpp"
#include "Lib/Timer.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Parse/SMTLIB2.hpp"
#include "Parse/TPTP.hpp"

#include "AnswerExtractor.hpp"
#include "InterpolantMinimizer.hpp"
#include "InterpolantMinimizerNew.hpp"
#include "Interpolants.hpp"
#include "InterpolantsNew.hpp"
#include "LaTeX.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "Statistics.hpp"
#include "TPTPPrinter.hpp"
#include "UIHelper.hpp"

#include "Lib/RCPtr.hpp"
#include "Lib/List.hpp"
#include "Lib/ScopedPtr.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace Saturation;
using namespace std;

bool outputAllowed(bool debug)
{
#if VDEBUG
  if(debug){ return true; }
#endif

  // spider and smtcomp output modes are generally silent
  return !Lib::env.options || (Lib::env.options->outputMode()!=Shell::Options::Output::SPIDER
                               && Lib::env.options->outputMode()!=Shell::Options::Output::SMTCOMP );
}

void reportSpiderFail()
{
  reportSpiderStatus('!');
}

void reportSpiderStatus(char status)
{
  using namespace Lib;

  if(Lib::env.options && Lib::env.options->outputMode() == Shell::Options::Output::SPIDER) {
    env.beginOutput();
    env.out() << status << " "
      << (Lib::env.options ? Lib::env.options->problemName() : "unknown") << " "
      << (Lib::env.timer ? Lib::env.timer->elapsedDeciseconds() : 0) << " "
      << (Lib::env.options ? Lib::env.options->testId() : "unknown") << "\n";
    env.endOutput();
  }
}

bool szsOutputMode() {
  return (Lib::env.options && Lib::env.options->outputMode() == Shell::Options::Output::SZS);
}

ostream& addCommentSignForSZS(ostream& out)
{
  if (szsOutputMode()) {
    out << "% ";
    if (Lib::env.options && Lib::env.options->multicore() != 1) {
      out << "(" << getpid() << ")";
    }
  }
  return out;
}

bool UIHelper::s_haveConjecture=false;
bool UIHelper::s_proofHasConjecture=true;

bool UIHelper::s_expecting_sat=false;
bool UIHelper::s_expecting_unsat=false;

void UIHelper::outputAllPremises(ostream& out, UnitList* units, vstring prefix)
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
  while (uit.hasNext()) {
    Unit* u = uit.next();
    toDo.push(UnitSpec(u));
  }

  while (toDo.isNonEmpty()) {
    UnitSpec us = toDo.pop();
    UnitSpecIterator pars = InferenceStore::instance()->getParents(us);
    while (pars.hasNext()) {
      UnitSpec par = pars.next();
      if (seen.contains(par)) {
	continue;
      }
      prems.push(par);
      toDo.push(par);
      seen.insert(par);
    }
  }

  std::sort(prems.begin(), prems.end(), UIHelper::unitSpecNumberComparator);

  Stack<UnitSpec>::BottomFirstIterator premIt(prems);
  while (premIt.hasNext()) {
    UnitSpec prem = premIt.next();
    out << prefix << prem.toString() << endl;
  }
#endif
}

void UIHelper::outputSaturatedSet(ostream& out, UnitIterator uit)
{
  CALL("UIHelper::outputSaturatedSet");

  addCommentSignForSZS(out);
  out << "# SZS output start Saturation." << endl;

  while (uit.hasNext()) {
    Unit* cl = uit.next();
    out << TPTPPrinter::toString(cl) << endl;
  }

  addCommentSignForSZS(out);
  out << "# SZS output end Saturation." << endl;
} // outputSaturatedSet

UnitList* parsedUnits;

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
  env.statistics->phase = Statistics::PARSING;

  SMTLIBLogic smtLibLogic = SMT_UNDEFINED;

  vstring inputFile = opts.inputFile();

  istream* input;
  if (inputFile=="") {
    input=&cin;
  } else {
    // CAREFUL: this might not be enough if the ifstream (re)allocates while being operated
    BYPASSING_ALLOCATOR; 
    
    input=new ifstream(inputFile.c_str());
    if (input->fail()) {
      USER_ERROR("Cannot open problem file: "+inputFile);
    }
  }

  UnitList* units;
  switch (opts.inputSyntax()) {
  case Options::InputSyntax::TPTP:
    {
      Parse::TPTP parser(*input);
      try{
        parser.parse();
      }
      catch (UserErrorException& exception) {
        vstring msg = exception.msg();
        throw Parse::TPTP::ParseErrorException(msg,parser.lineNumber());
      }
      units = parser.units();
      s_haveConjecture=parser.containsConjecture();
    }
    break;
  case Options::InputSyntax::SMTLIB2:
  {
	  Parse::SMTLIB2 parser(opts);
	  parser.parse(*input);
          Unit::onParsingEnd();

	  units = parser.getFormulas();
    smtLibLogic = parser.getLogic();
	  s_haveConjecture=false;

#if VDEBUG
	  const vstring& expected_status = parser.getStatus();
	  if (expected_status == "sat") {
	    s_expecting_sat = true;
	  } else if (expected_status == "unsat") {
	    s_expecting_unsat = true;
	  }
#endif

	  break;
  }
/*
  case Options::InputSyntax::MPS:
  case Options::InputSyntax::NETLIB:
  case Options::InputSyntax::HUMAN:
  {
    cout << "This is not supported yet";
    NOT_IMPLEMENTED;
   }
*/
   break;
  }

  if (inputFile!="") {
    BYPASSING_ALLOCATOR;
    
    delete static_cast<ifstream*>(input);
    input=0;
  }

  // parsedUnits = units->copy();

  Problem* res = new Problem(units);
  res->setSMTLIBLogic(smtLibLogic);

  env.statistics->phase=Statistics::UNKNOWN_PHASE;
  return res;
}

/*
static void printInterpolationProofTask(ostream& out, Formula* intp, Color avoid_color, bool negate)
{
  CALL("printInterpolationProofTask");

  UIHelper::outputSortDeclarations(out);
  UIHelper::outputSymbolDeclarations(out);

  UnitList::Iterator uit(parsedUnits);
  while (uit.hasNext()) {
    Unit* u = uit.next();

    if (u->inheritedColor() != avoid_color) { // TODO: this does not work, since some inherited colors are modified destructively by the interpolation extraction code
      Unit* toPrint = u;
      if (toPrint->isClause()) { // need formulas, for the many sorted case
        Formula* f = Formula::fromClause(toPrint->asClause());
        toPrint = new FormulaUnit(f,u->inference(),Unit::AXIOM);
      } else {
        u->setInputType(Unit::AXIOM); // need it to be axiom in any case; the interpolant will be the conjecture
      }

      out << TPTPPrinter::toString(toPrint) << endl;
    }
  }

  FormulaUnit* intpUnit = new FormulaUnit(negate ? new NegatedFormula(intp) : intp,new Inference0(Inference::INPUT),Unit::CONJECTURE);
  out << TPTPPrinter::toString(intpUnit) << "\n";
}
*/

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
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unsat" << endl;
      return;
    }
    addCommentSignForSZS(out);
    out << "Refutation found. Thanks to " << env.options->thanks() << "!\n";
    if (szsOutputMode()) {
      out << "% SZS status " << (UIHelper::haveConjecture() ? ( UIHelper::haveConjectureInProof() ? "Theorem" : "ContradictoryAxioms" ) : "Unsatisfiable")
	  << " for " << env.options->problemName() << endl;
    }
    if (env.options->questionAnswering()!=Options::QuestionAnsweringMode::OFF) {
      ASS(env.statistics->refutation->isClause());
      AnswerExtractor::tryOutputAnswer(static_cast<Clause*>(env.statistics->refutation));
    }
    if (env.options->proof() != Options::Proof::OFF) {
      if (szsOutputMode()) {
        out << "% SZS output start Proof for " << env.options->problemName() << endl;
      }
      InferenceStore::instance()->outputProof(out, env.statistics->refutation);
      if (szsOutputMode()) {
        out << "% SZS output end Proof for " << env.options->problemName() << endl << flush;
      }
      // outputProof could have triggered proof minimization which might have cause inductionDepth to change (in fact, decrease)
      env.statistics->maxInductionDepth = env.statistics->refutation->inference().inductionDepth();
    }
    if (env.options->showInterpolant()!=Options::InterpolantMode::OFF) {
      ASS(env.statistics->refutation->isClause());

      Interpolants::removeConjectureNodesFromRefutation(env.statistics->refutation);
      Unit* formulifiedRefutation = Interpolants::formulifyRefutation(env.statistics->refutation);

      Formula* interpolant = nullptr;

      switch(env.options->showInterpolant()) {
      // new interpolation methods described in master thesis of Bernhard Gleiss
      case Options::InterpolantMode::NEW_HEUR:
        InterpolantsNew().removeTheoryInferences(formulifiedRefutation); // do this only once for each proof!

        // InterpolantMinimizerNew().analyzeLocalProof(formulifiedRefutation);

        interpolant = InterpolantsNew().getInterpolant(formulifiedRefutation, InterpolantsNew::UnitWeight::VAMPIRE);
        break;
      case Options::InterpolantMode::NEW_OPT:
#if VZ3
        InterpolantsNew().removeTheoryInferences(formulifiedRefutation); // do this only once for each proof!
        interpolant = InterpolantMinimizerNew().getInterpolant(formulifiedRefutation, InterpolantsNew::UnitWeight::VAMPIRE);
#else
        NOT_IMPLEMENTED;
#endif
        break;

      case Options::InterpolantMode::OLD:
        interpolant = Interpolants().getInterpolant(formulifiedRefutation);
        break;
        
      case Options::InterpolantMode::OLD_OPT:
        Interpolants::fakeNodesFromRightButGrayInputsRefutation(formulifiedRefutation); // grey right input formulas are artificially made children of proper blue parents
        interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(formulifiedRefutation);
        
        /*
        Formula* oldInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, true, true, "Original interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
        Formula* interpolant = InterpolantMinimizer(InterpolantMinimizer::OT_WEIGHT, false, true, "Minimized interpolant weight").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
        InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, true, true, "Original interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
        Formula* cntInterpolant = InterpolantMinimizer(InterpolantMinimizer::OT_COUNT, false, true, "Minimized interpolant count").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
        Formula* quantInterpolant =  InterpolantMinimizer(InterpolantMinimizer::OT_QUANTIFIERS, false, true, "Minimized interpolant quantifiers").getInterpolant(static_cast<Clause*>(env.statistics->refutation));
        */

        break;
      case Options::InterpolantMode::OFF:
        ASSERTION_VIOLATION;
      }

      out << "Symbol-weight minimized interpolant: " << TPTPPrinter::toString(interpolant) << endl;
      out << "Actual weight: " << interpolant->weight() << endl;
      out<<endl;
    }

    if (env.options->latexOutput() != "off") {
      BYPASSING_ALLOCATOR; // for ofstream 
      ofstream latexOut(env.options->latexOutput().c_str());

      LaTeX formatter;
      latexOut << formatter.refutationToString(env.statistics->refutation);
    }

    ASS(!s_expecting_sat);

    break;
  case Statistics::TIME_LIMIT:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unknown" << endl;
      return;
    }
    addCommentSignForSZS(out);
    out << "Time limit reached!\n";
    break;
  case Statistics::MEMORY_LIMIT:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unknown" << endl;
      return;
    }
#if VDEBUG
    Allocator::reportUsageByClasses();
#endif
    addCommentSignForSZS(out);
    out << "Memory limit exceeded!\n";
    break;
  case Statistics::ACTIVATION_LIMIT: {
    addCommentSignForSZS(out);
    out << "Activation limit reached!\n";

    // HERE ADD MORE

    break;
  }
  case Statistics::REFUTATION_NOT_FOUND:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unknown" << endl;
      return;
    }
    addCommentSignForSZS(out);
    env.statistics->explainRefutationNotFound(out);
    break;
  case Statistics::SATISFIABLE:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "sat" << endl;
      return;
    }
    outputSatisfiableResult(out);

    ASS(!s_expecting_unsat);

    break;
  case Statistics::SAT_SATISFIABLE:
    outputSatisfiableResult(out);
    break;
  case Statistics::SAT_UNSATISFIABLE:
    out<<"good job\n";
    break;
  case Statistics::INAPPROPRIATE:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unknown" << endl;
      return;
    }
    addCommentSignForSZS(out);
    out << "Terminated due to inappropriate strategy.\n";
    break;
  case Statistics::UNKNOWN:
    if(env.options->outputMode() == Options::Output::SMTCOMP){
      out << "unknown" << endl;
      return;
    }
    addCommentSignForSZS(out);
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

  //out << "Satisfiable!\n";
  if (szsOutputMode() && !satisfiableStatusWasAlreadyOutput) {
    out << "% SZS status " << ( UIHelper::haveConjecture() ? "CounterSatisfiable" : "Satisfiable" )
	  <<" for " << env.options->problemName() << endl;
  }
  if (!env.statistics->model.empty()) {
    if (szsOutputMode()) {
	out << "% SZS output start FiniteModel for " << env.options->problemName() << endl;
    }
    out << env.statistics->model;
    if (szsOutputMode()) {
	out << "% SZS output end FiniteModel for " << env.options->problemName() << endl;
    }
  }
  else //if (env.statistics->saturatedSet)
       /* -- MS: it's never incorrect to print the empty one, in fact this prevents us from losing
        * points at CASC when the input gets completely emptied, by e.g. preprocessing
        */
  {
    outputSaturatedSet(out, pvi(UnitList::Iterator(env.statistics->saturatedSet)));
  }
}

/**
 * Output to @b out all symbol declarations for the current signature.
 * Symbols having default types will not be output.
 * @author Andrei Voronkov
 * @since 03/07/2013 Manchester
 */
void UIHelper::outputSymbolDeclarations(ostream& out)
{
  CALL("UIHelper::outputSymbolDeclarations");

  Signature& sig = *env.signature;

  unsigned funcs = sig.functions();
  for (unsigned i=0; i<funcs; ++i) {
    if (!env.options->showFOOL()) {
      if (env.signature->isFoolConstantSymbol(true,i) || env.signature->isFoolConstantSymbol(false,i)) {
        continue;
      }
    }
    outputSymbolTypeDeclarationIfNeeded(out, true, i);
  }
  unsigned preds = sig.predicates();
  for (unsigned i=0; i<preds; ++i) {
    outputSymbolTypeDeclarationIfNeeded(out, false, i);
  }
} // UIHelper::outputSymbolDeclarations

/**
 * Output to @b out a function or a predicate symbol declaration.
 * Symbols having default types will not be output.
 * @author Andrei Voronkov
 * @since 03/07/2013 Manchester
 */
void UIHelper::outputSymbolTypeDeclarationIfNeeded(ostream& out, bool function, unsigned symNumber)
{
  CALL("UIHelper::outputSymbolTypeDeclarationIfNeeded");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);

  if (sym->interpreted()) {
    //there is no need to output type definitions for interpreted symbols
    return;
  }

  if (sym->overflownConstant()) {
    // don't output definitions of numbers; not even big ones
    return;
  }

  unsigned dummy;
  if (Theory::tuples()->findProjection(symNumber, !function, dummy)) {
    return;
  }

  if (function) {
    unsigned sort = env.signature->getFunction(symNumber)->fnType()->result();
    if (env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::TUPLE)) {
      return;
    }
  }

  OperatorType* type = function ? sym->fnType() : sym->predType();

  if (type->isAllDefault()) {
    return;
  }

  out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ", type, "
      << sym->name() << ": ";

  unsigned arity = sym->arity();
  if (arity>0) {
    if (arity==1) {
      out << env.sorts->sortName(type->arg(0));
    }
    else {
      out << "(";
      for (unsigned i=0; i<arity; i++) {
	if (i>0) {
	  out << " * ";
	}
	out << env.sorts->sortName(type->arg(i));
      }
      out << ")";
    }
    out << " > ";
  }
  if (function) {
    out << env.sorts->sortName(sym->fnType()->result());
  }
  else {
    out << "$o";
  }
  out << ")." << endl;
}

/**
 * Output to @b out all sort declarations for the current signature.
 * Built-in sorts and structures sorts will not be output.
 * @author Evgeny Kotelnikov
 * @since 04/09/2015 Gothneburg
 */
void UIHelper::outputSortDeclarations(ostream& out)
{
  CALL("UIHelper::outputSortDeclarations");

  unsigned sorts = (*env.sorts).count();
  for (unsigned sort = Sorts::SRT_BOOL; sort < sorts; ++sort) {
    if (sort < Sorts::FIRST_USER_SORT && ((sort != Sorts::SRT_BOOL) || !env.options->showFOOL())) {
      continue;
    }
    if ((*env.sorts).isStructuredSort(sort)) {
      continue;
    }
    out << "tff(type_def_" << sort << ", type, " << env.sorts->sortName(sort) << ": $tType)." << endl;
  }
} // UIHelper::outputSortDeclarations
} // namespace Shell
