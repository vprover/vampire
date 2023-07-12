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
#include "Debug/TimeProfiling.hpp"
#include "Lib/VString.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Allocator.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Parse/SMTLIB2.hpp"
#include "Parse/TPTP.hpp"

#include "AnswerExtractor.hpp"
#include "InterpolantMinimizer.hpp"
#include "Interpolants.hpp"
#include "LaTeX.hpp"
#include "LispLexer.hpp"
#include "LispParser.hpp"
#include "Options.hpp"
#include "Statistics.hpp"
#include "TPTPPrinter.hpp"
#include "UIHelper.hpp"

#include "SAT/Z3Interfacing.hpp"

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
  if (debug) { return true; }
#endif

  // spider and smtcomp output modes are generally silent
  return !Lib::env.options ||
    (
     Lib::env.options->outputMode() != Shell::Options::Output::SPIDER
     && Lib::env.options->outputMode() != Shell::Options::Output::SMTCOMP 
     && Lib::env.options->outputMode() != Shell::Options::Output::UCORE
     );
}

void reportSpiderFail()
{
  reportSpiderStatus('!');
}

void reportSpiderStatus(char status)
{
#if VZ3
  if (UIHelper::spiderOutputDone) {
    return;
  }
  if (Lib::env.options && Lib::env.options->outputMode() != Shell::Options::Output::SPIDER) {
    return;
  }

  UIHelper::spiderOutputDone = true;

  // compute Vampire Z3 version and commit
  vstring version = VERSION_STRING;
  size_t versionPosition = version.find("commit ") + strlen("commit ");
  size_t afterVersionPosition = version.find(" ",versionPosition + 1);
  vstring commitNumber = version.substr(versionPosition,afterVersionPosition - versionPosition);
  vstring z3Version = Z3Interfacing::z3_full_version();
  size_t spacePosition = z3Version.find(" ");
  if (spacePosition != string::npos) {
    z3Version = z3Version.substr(0,spacePosition);
  }

  vstring problemName = Lib::env.options->problemName();
  Timer* timer = Lib::env.timer;

  env.beginOutput();
  env.out()
    << status << " "
    << (problemName.length() == 0 ? "unknown" : problemName) << " "
    << (timer ? timer->elapsedDeciseconds() : 0) << " "
    << (timer ? timer->elapsedMegaInstructions() : 0) << " "
    << Allocator::getUsedMemory()/1048576 << " "
    << (Lib::env.options ? Lib::env.options->testId() : "unknown") << " "
    << commitNumber << ':' << z3Version << endl;
  env.endOutput();
#endif
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

bool UIHelper::portfolioParent=false;
bool UIHelper::satisfiableStatusWasAlreadyOutput=false;

bool UIHelper::spiderOutputDone = false;
  
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

// String utility function that probably belongs elsewhere
static bool hasEnding (vstring const &fullString, vstring const &ending) {
    if (fullString.length() >= ending.length()) {
        return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
    } else {
        return false;
    }
}

UnitList* UIHelper::tryParseTPTP(istream* input)
{
      Parse::TPTP parser(*input);
      try{
        parser.parse();
      }
      catch (UserErrorException& exception) {
        vstring msg = exception.msg();
        throw Parse::TPTP::ParseErrorException(msg,parser.lineNumber());
      }
      s_haveConjecture=parser.containsConjecture();
      return parser.units();
}

UnitList* UIHelper::tryParseSMTLIB2(const Options& opts,istream* input,SMTLIBLogic& smtLibLogic)
{
          Parse::SMTLIB2 parser(opts);
          parser.parse(*input);
          Unit::onParsingEnd();

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
          return parser.getFormulas();
}

// Call this function to report a parsing attempt has failed and to reset the input
template<typename T>
void resetParsing(T exception, vstring inputFile, istream*& input,vstring nowtry)
{
  if (env.options->mode()!=Options::Mode::SPIDER) {
    env.beginOutput();
    addCommentSignForSZS(env.out());
    env.out() << "Failed with\n";
    addCommentSignForSZS(env.out());
    exception.cry(env.out());
    addCommentSignForSZS(env.out());
    env.out() << "Trying " << nowtry  << endl;
    env.endOutput();
  }

  BYPASSING_ALLOCATOR;
  delete static_cast<ifstream*>(input);
  input=new ifstream(inputFile.c_str());
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
    
  TIME_TRACE(TimeTrace::PARSING);
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

  UnitList* units = nullptr;
  switch (opts.inputSyntax()) {
  case Options::InputSyntax::AUTO:
    {
       // First lets pick a place to start based on the input file name
       bool smtlib = hasEnding(inputFile,"smt") || hasEnding(inputFile,"smt2");
       Options::Mode mode = env.options->mode();
       
       if (smtlib){
         if (mode != Options::Mode::SPIDER && mode != Options::Mode::PROFILE) {
           env.beginOutput();
           addCommentSignForSZS(env.out());
           env.out() << "Running in auto input_syntax mode. Trying SMTLIB2\n";
           env.endOutput();
         }
         try{
           units = tryParseSMTLIB2(opts,input,smtLibLogic);
         }
         catch (UserErrorException& exception) {
           resetParsing(exception,inputFile,input,"TPTP");
           units = tryParseTPTP(input);
         }
         catch (LexerException& exception) {
           resetParsing(exception,inputFile,input,"TPTP");
           units = tryParseTPTP(input);
         }
         catch (LispParser::Exception& exception) {
           resetParsing(exception,inputFile,input,"TPTP");
           units = tryParseTPTP(input);
         }

       }
       else {
         if (mode != Options::Mode::SPIDER && mode != Options::Mode::PROFILE) {
           env.beginOutput();
           addCommentSignForSZS(env.out());
           env.out() << "Running in auto input_syntax mode. Trying TPTP\n";
           env.endOutput();
         }
         try{
           units = tryParseTPTP(input); 
         }
         catch (Parse::TPTP::ParseErrorException& exception) {
           resetParsing(exception,inputFile,input,"SMTLIB2"); 
           units = tryParseSMTLIB2(opts,input,smtLibLogic); 
         }
       }
       
    }
    break;
  case Options::InputSyntax::TPTP:
    units = tryParseTPTP(input);
    break;
  case Options::InputSyntax::SMTLIB2:
    units = tryParseSMTLIB2(opts,input,smtLibLogic);
    break;
  }
  if (inputFile!="") {
    BYPASSING_ALLOCATOR;

    delete static_cast<ifstream*>(input);
    input=0;
  }

  Problem* res = new Problem(units);
  res->setSMTLIBLogic(smtLibLogic);
  env.statistics->phase=Statistics::UNKNOWN_PHASE;
  env.setMainProblem(res);
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
    if(env.options->outputMode() == Options::Output::SMTCOMP){ 
      out << "unsat" << endl;
      return;
    }
    if(env.options->outputMode() == Options::Output::UCORE){
      out << "unsat" << endl;
      InferenceStore::instance()->outputUnsatCore(out, env.statistics->refutation);
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
        Interpolants().removeTheoryInferences(formulifiedRefutation); // do this only once for each proof!
        interpolant = Interpolants().getInterpolant(formulifiedRefutation, Interpolants::UnitWeight::VAMPIRE);
        break;
#if VZ3
      case Options::InterpolantMode::NEW_OPT:

        Interpolants().removeTheoryInferences(formulifiedRefutation); // do this only once for each proof!
        interpolant = InterpolantMinimizer().getInterpolant(formulifiedRefutation, Interpolants::UnitWeight::VAMPIRE);
        break;
#endif
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

  unsigned typeCons = sig.typeCons();
  for (unsigned i=0; i<typeCons; ++i) {
    outputSymbolTypeDeclarationIfNeeded(out, false, true, i);
  }
  unsigned funcs = sig.functions();
  for (unsigned i=0; i<funcs; ++i) {
    if (!env.options->showFOOL()) {
      if (env.signature->isFoolConstantSymbol(true,i) || env.signature->isFoolConstantSymbol(false,i)) {
        continue;
      }
    }
    outputSymbolTypeDeclarationIfNeeded(out, true, false, i);
  }
  unsigned preds = sig.predicates();
  for (unsigned i=0; i<preds; ++i) {
    outputSymbolTypeDeclarationIfNeeded(out, false, false, i);
  }
} // UIHelper::outputSymbolDeclarations

/**
 * Output to @b out a function or a predicate symbol declaration.
 * Symbols having default types will not be output.
 * @author Andrei Voronkov
 * @since 03/07/2013 Manchester
 */
void UIHelper::outputSymbolTypeDeclarationIfNeeded(ostream& out, bool function, bool typeCon, unsigned symNumber)
{
  CALL("UIHelper::outputSymbolTypeDeclarationIfNeeded");

  Signature::Symbol* sym;

  if(function){
    sym = env.signature->getFunction(symNumber);
  } else if(typeCon){
    sym = env.signature->getTypeCon(symNumber);
  } else {
    sym = env.signature->getPredicate(symNumber);    
  }

  if (typeCon && (env.signature->isArrayCon(symNumber) ||
                  env.signature->isTupleCon(symNumber))){
    return;
  }

  if(typeCon && env.signature->isDefaultSortCon(symNumber) && 
    (!env.signature->isBoolCon(symNumber) || !env.options->showFOOL())){
    return;
  }

  if (sym->interpreted()) {
    //there is no need to output type definitions for interpreted symbols
    return;
  }

  if (sym->overflownConstant()) {
    // don't output definitions of numbers; not even big ones
    return;
  }

  unsigned dummy;
  if (!typeCon && Theory::tuples()->findProjection(symNumber, !function, dummy)) {
    return;
  }

  if (function) {
    TermList sort = env.signature->getFunction(symNumber)->fnType()->result();
    if (sort.isTupleSort()) {
      return;
    }
  }

  OperatorType* type = function ? sym->fnType() : 
               (typeCon ? sym->typeConType() : sym->predType());

  if (type->isAllDefault()) {//TODO required
    return;
  }

  //out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ", type, "
  //    << sym->name() << ": ";

  vstring symName = sym->name();
  if(typeCon && env.signature->isBoolCon(symNumber)){
    ASS(env.options->showFOOL());
    symName = "$bool";
  }

  //don't output type of app. It is an internal Vampire thing
  if(!(function && env.signature->isAppFun(symNumber))){
    out << (env.getMainProblem()->isHigherOrder() ? "thf(" : "tff(")
        << (function ? "func" : (typeCon ?  "type" : "pred")) 
        << "_def_" << symNumber << ", type, "
        << symName << ": ";
    out << type->toString();
    out << ")." << endl;
  }
  //out << ")." << endl;
}

} // namespace Shell
