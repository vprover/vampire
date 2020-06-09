
/*
 * File UIHelper.cpp.
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
 * @file UIHelper.cpp
 * Implements class UIHelper.
 */

#include <fstream>

#include <stdlib.h>
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
#include "SimplifyProver.hpp"
#include "Statistics.hpp"
#include "TPTPPrinter.hpp"
#include "UIHelper.hpp"
// #include "SMTPrinter.hpp"

#include "Lib/RCPtr.hpp"
#include "Lib/List.hpp"
#include "Lib/ScopedPtr.hpp"

#if GNUMP
#include "Kernel/Assignment.hpp"
#include "Kernel/Constraint.hpp"
#include "Kernel/Signature.hpp"

#include "ConstraintReaderBack.hpp"
#include "Shell/SMTLEX.hpp"
#include "Shell/SMTPAR.hpp"
#include "Preprocess.hpp"

#include "MPSLib/Gmputils.h"
#include "MPSLib/Model.h"
#include "MPSLib/Mpsinput.h"

#include <algorithm>
#include <vector>
#include <list>
#endif

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
  case Options::InputSyntax::SIMPLIFY:
  {
    Shell::LispLexer lexer(*input);
    Shell::LispParser parser(lexer);
    LispParser::Expression* expr = parser.parse();
    SimplifyProver simplify;
    units = simplify.units(expr);
  }
  break;
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
  case Options::InputSyntax::SMTLIB:
    /*  {
        Parse::SMTLIB parser(opts);
        parser.parse(*input);
        units = parser.getFormulas();
        s_haveConjecture=true;
      }
      break; */
    if (outputAllowed()) {
      env.beginOutput();
      addCommentSignForSZS(env.out());
      env.out() << "Vampire no longer supports the old smtlib format, trying with smtlib2 instead." << endl;
      env.endOutput();
    }
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

#if GNUMP
/**
 * Add input constraints into the empty @c constraints list.
 */
ConstraintRCList* UIHelper::getInputConstraints(const Options& opts)
{
  CALL("UIHelper::getInputConstraints");

  TimeCounter tc(TC_PARSING);
  env.statistics->phase = Statistics::PARSING;

  vstring inputFile = env.options->inputFile();

  ScopedPtr<std::ifstream> inputScoped;
  istream * input;
  if (inputFile=="") {
     input=&cin;
   } else {
     inputScoped=new ifstream(inputFile.c_str());
     input = inputScoped.ptr();
     if (input->fail()) {
       USER_ERROR("Cannot open problem file: "+inputFile);
     }
   }

  ConstraintRCList* res;

  switch(env.options->inputSyntax()) {
  case Options::InputSyntax::TPTP:
    USER_ERROR("Format not supported for BPA");
    break;
#if 0
  case Options::InputSyntax::SMTLIB:
  case Options::InputSyntax::SMTLIB2:
  {
    Parse::SMTLIB parser(opts);
    parser.parse(*input);
    UnitList* ulist = parser.getFormulas();
    UnitList::Iterator ite(ulist);
    while (ite.hasNext())
    {
      Unit* u = ite.next();
      if ( !u->isClause()) {
	Formula* f = u->getFormula();
	std::cout << f->toString();
      }


    }
    ASSERTION_VIOLATION;
    s_haveConjecture=true;
    SMTConstraintReader rdr(parser);
    res = rdr.constraints();
    break;
    
    /*
    std::cout << "doing the constraint reading" << std::endl;
    Parse::SMTLIB parser1(*env.options);
  
    vstring inputFile = env.options->inputFile();
    std::cout << inputFile << std::endl;
    istream* input;
    if (inputFile=="") {
      input=&cin;
    } else {
      input=new ifstream(inputFile.c_str());
      if (input->fail()) {
	USER_ERROR("Cannot open problem file: "+inputFile);
      }
    }
  
    parser1.parse(*input);
    std::cout << parser1.getLispFormula()->toString() << std::endl;
     */
  }
#endif
  case Options::InputSyntax::SMTLIB:
  {
    SMTLexer lex(*input);
    SMTParser parser(lex);
    ConstraintReader rdr(parser);
    res = rdr.constraints();
    break;
  }
  case Options::InputSyntax::SMTLIB2:
    {
      Parse::SMTLIB2 parser(opts, Parse::SMTLIB2::DECLARE_SYMBOLS);
      parser.parse(*input);
      SMTLib2ConstraintReader rdr(parser);
      res = rdr.constraints();
      break;

    }
  case Options::InputSyntax::MPS:
  {
    Model* m = new Model; 
    MpsInput* mpsin = new MpsInput;
        
    bool success = mpsin->readMps(env.options->inputFile().c_str(), m);
   // m->print(std::cout);

    ASS_EQ(success,true);
    MpsConstraintReader creader(*m);
    res = creader.constraints();

#if 0
    ConstraintRCList::Iterator ite(res);
    while (ite.hasNext())
	std::cout << ite.next()->toString() << std::endl;
    throw TimeLimitExceededException();
    ASSERTION_VIOLATION;
#endif 
    break;
  }
  case Options::InputSyntax::HUMAN:
    USER_ERROR("human syntax is not supported as input syntax");
  case Options::InputSyntax::NETLIB:
 // case Options::InputSyntax::SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }

  env.statistics->inputConstraints = res->length();
  env.statistics->inputVariables = env.signature->vars();

  return res;
}

/**
 * Preprocess @c inputConstraints into @c constraints.
 */
ConstraintRCList* UIHelper::getPreprocessedConstraints(const ConstraintRCList* inputConstraints)
{
  CALL("UIHelper::getPreprocessedConstraints/2");

  TimeCounter tc(TC_PREPROCESSING);
  env.statistics->phase = Statistics::PREPROCESSING;

  Preprocess prepr(*env.options);
  ConstraintRCList* constraints = ConstraintRCList::copy(inputConstraints);
  prepr.preprocess(constraints);
  
  return constraints;
}

/**
 * Add preprocessed input constraints into the empty @c constraints list.
 */
ConstraintRCList* UIHelper::getPreprocessedConstraints(const Options& opts)
{
  CALL("UIHelper::getPreprocessedConstraints/1");

  ConstraintRCList* inpConstraints(getInputConstraints(opts));
  return getPreprocessedConstraints(inpConstraints);
}

/**
 * Into stream @c out output @c constraint in format @b syntax.
 */
void UIHelper::outputConstraint(const Constraint& constraint, ostream& out, Options::InputSyntax syntax)
{
  CALL("UIHelper::outputConstraint");

  switch(syntax) {
  case Options::InputSyntax::HUMAN:
    outputConstraintInHumanFormat(constraint, out);
    // outputConstraintInSMTFormat(constraint,out);
    return;
  case Options::InputSyntax::SMTLIB:
      outputConstraintInSMTFormat(constraint,out);
      return;
  case Options::InputSyntax::MPS:
  case Options::InputSyntax::NETLIB:
  case Options::InputSyntax::SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }

}

void UIHelper::outputConstraintInHumanFormat(const Constraint& constraint, ostream& out)
{
  CALL("UIHelper::outputConstraintInHumanFormat");

  /* 
   * Constraint::CoeffIterator coeffs = constraint.coeffs();
 

  switch(constraint.type()) {
  case CT_EQ:
    out << "( = "; break;
  case CT_GR:
    out << "( >"; break;
  case CT_GREQ:
    out << "( >="; break;
  }
  
  unsigned closedP = 0; 
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ) 
  {
    out << " (+";
    closedP ++;
    if (constraint.freeCoeff().isNegativeAssumingNonzero())
	out<< " " << -constraint.freeCoeff().native() <<" ";
    if (constraint.freeCoeff().isPositiveAssumingNonzero()) 
	out<< " (~ " << constraint.freeCoeff().native() <<")";
  }
    
  while (coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
     if (coeffs.hasNext()) {
	out << " (+ ";
	closedP++;
    }
    if (coeff.value<CoeffNumber::zero()) {
	out << " (* ( ~ " << -coeff.value << " ) " << env.signature->varName(coeff.var) << ")";
    }
    else {
	out <<" (* "<< coeff.value << " " << env.signature->varName(coeff.var) << " )";
    }
   
  }
  
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ )
      out <<  "";
  
  while (closedP!=0)
  {
    out <<  ")"; 
    closedP--;
    }
   out << " 0 )";
  
 */ 
  Constraint::CoeffIterator coeffs = constraint.coeffs();
  if (!coeffs.hasNext()) {
    out << "0 ";
  }
  while (coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
    if (coeff.value<CoeffNumber::zero()) {
	out << "(" << coeff.value << "*" << env.signature->varName(coeff.var) << ") ";
    }
    else {
	out << coeff.value << "*" << env.signature->varName(coeff.var) << " ";
    }
    if (coeffs.hasNext()) {
	out << "+ ";
    }
  }
  switch(constraint.type()) {
  case CT_EQ:
    out << "="; break;
  case CT_GR:
    out << ">"; break;
  case CT_GREQ:
    out << ">="; break;
  }
  out << " " << constraint.freeCoeff(); 
}


void UIHelper::outputConstraintInSMTFormat(const Constraint& constraint, ostream& out)
{
  CALL("UIHelper::outputConstraintInSMTFormat");

  Constraint::CoeffIterator coeffs = constraint.coeffs();
  
 /* 
  if (!coeffs.hasNext()) {
    out << " 0 ";
  }
  */
  switch(constraint.type()) {
  case CT_EQ:
    out << "( = "; break;
  case CT_GR:
    out << "( >"; break;
  case CT_GREQ:
    out << "( >="; break;
  }
  
  unsigned closedP = 0; 
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ) 
  {
    out << " (+";
    closedP ++;
    if (constraint.freeCoeff().isNegativeAssumingNonzero())
	out <<  " " << -constraint.freeCoeff().native()  << " ";
    if (constraint.freeCoeff().isPositiveAssumingNonzero()) 
	out <<  " (~ " << constraint.freeCoeff().native()  << ")";
  }
    
  while (coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
     if (coeffs.hasNext()) {
	out << " (+ ";
	closedP++;
	 
    }
    
    if (coeff.value<CoeffNumber::zero()) {
	
	out << " (* ( ~ " << -coeff.value << " ) " << env.signature->varName(coeff.var) << ")";
    }
    else {
	out <<" (* "<< coeff.value << " " << env.signature->varName(coeff.var) << " )";
    }
   
  }
  
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ )
      out <<  "";
  
  while (closedP!=0)
  {
    out <<  ")"; 
    closedP--;
    }
   out << " 0 )";
  
 /* if (constraint.freeCoeff().isNegative() || constraint.freeCoeff() == CoeffNumber::zero() )
    out << "(~" << -constraint.freeCoeff() <<") )";
  else 
    out << " " << constraint.freeCoeff() <<" )";*/
}

/**
 * Into stream @c out output @c constraints in format @b syntax.
 */
void UIHelper::outputConstraints(ConstraintList* constraints, ostream& out, Options::InputSyntax syntax)
{ 
  CALL("UIHelper::outputConstraints");

  switch(syntax) {
  case Options::InputSyntax::HUMAN:
  {
    ConstraintList::Iterator ite(constraints);
    while (ite.hasNext())
    {
	outputConstraint(*ite.next(), out, syntax);
	out << endl;
    }
    return;
  }
  case Options::InputSyntax::SMTLIB:
  {
     out << " (benchmark  SOMENAME" << endl;
    out << " :source {converted from MIPLIB} " << endl;
    out << " :status unknown " << endl;
    out << " :category { industrial } " << endl;
    out << " :logic QF_LRA " << endl;
    
    ConstraintList::Iterator fun(constraints);
    std::list<vstring> uni;

    while (fun.hasNext())
    {
	Constraint::CoeffIterator coeffs = fun.next()->coeffs();
	 while (coeffs.hasNext()) {
	     env.signature->varName(coeffs.next().var);
	     uni.push_back(env.signature->varName(coeffs.next().var));
	  //out << ":extrafuns ((" << env.signature->varName(coeffs.next().var) << " Real )) " << endl; 
	}
	
    }

    std::vector<vstring> myvector (uni.begin(),uni.end());
    std::vector<vstring>::iterator ite;
    ite = unique(myvector.begin(),myvector.end());
    myvector.resize( ite - myvector.begin() );
    for (ite=myvector.begin(); ite!=myvector.end(); ++ite)
	out << " " << *ite;
    
    out << ":formula (and "; 
    ConstraintList::Iterator it(constraints);
    while (it.hasNext()) {
      outputConstraint(*it.next(), out, syntax);
      out << " \n";
    }
    
    out <<  ") )"<< endl;
    return;
  }
  
  case Options::InputSyntax::MPS:
  case Options::InputSyntax::NETLIB:
  case Options::InputSyntax::SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }
}

void UIHelper::outputAssignment(Assignment& assignemt, ostream& out, Shell::Options::InputSyntax syntax)
{
  CALL("UIHelper::outputAssignment");

  switch(syntax) {
  case Options::InputSyntax::HUMAN:
  case Options::InputSyntax::MPS:
  case Options::InputSyntax::SMTLIB:
  {
    VarIterator vars = assignemt.getAssignedVars();
    while (vars.hasNext()) {
      Var v = vars.next();
      out << env.signature->varName(v) << ": " << assignemt[v] << endl;
    }
    return;
  }
  case Options::InputSyntax::NETLIB:
  case Options::InputSyntax::SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }
}

#endif //GNUMP

} // namespace Shell


