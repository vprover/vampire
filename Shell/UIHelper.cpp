/**
 * @file UIHelper.cpp
 * Implements class UIHelper.
 */

#include <string>
#include <fstream>

#include <stdlib.h>
#include <iostream>

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
#include "TPTPPrinter.hpp"
#include "UIHelper.hpp"

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

namespace Shell
{

using namespace Lib;
using namespace Kernel;
using namespace Saturation;
using namespace std;

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
    out << TPTPPrinter::toString(cl) << endl;
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
  
  case Options::IS_MPS:
  {
    break;
  } 
  break;
  case Options::IS_NETLIB:
  case Options::IS_SMTLIB2:
  case Options::IS_HUMAN:
  {
    cout<<"This is not supported yet";
    NOT_IMPLEMENTED;
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
      out << "Old interpolant: " << TPTPPrinter::toString(oldInterpolant) << endl;
      out << "Interpolant: " << TPTPPrinter::toString(interpolant) << endl;
      out << "Count minimized interpolant: " << TPTPPrinter::toString(cntInterpolant) << endl;
      out << "Quantifiers minimized interpolant: " << TPTPPrinter::toString(quantInterpolant) << endl;
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

#if GNUMP
/**
 * de aici am pus pentru bound propagation 
 */

/**
 * Add input constraints into the empty @c constraints list.
 */
ConstraintRCList* UIHelper::getInputConstraints(const Options& opts)
{
  CALL("UIHelper::getInputConstraints");

  TimeCounter tc(TC_PARSING);
  env.statistics->phase = Statistics::PARSING;

  string inputFile = env.options->inputFile();

  ScopedPtr<std::ifstream> inputScoped;
  istream * input;
  if(inputFile=="") {
     input=&cin;
   } else {
     inputScoped=new ifstream(inputFile.c_str());
     input = inputScoped.ptr();
     if(input->fail()) {
       USER_ERROR("Cannot open problem file: "+inputFile);
     }
   }

  ConstraintRCList* res;

  switch(env.options->inputSyntax()) {
  case Options::IS_TPTP:
    break;
#if 0
  case Options::IS_SMTLIB:
  case Options::IS_SMTLIB2:
  {
    Parse::SMTLIB parser(opts);
    parser.parse(*input);
    UnitList* ulist = parser.getFormulas();
    UnitList::Iterator ite(ulist);
    while(ite.hasNext())
    {
      Unit* u = ite.next();
      if ( !u->isClause()) {
	Formula* f = u->getFormula();
	std::cout<<f->toString();
      }


    }
    ASSERTION_VIOLATION;
    s_haveConjecture=true;
    SMTConstraintReader rdr(parser);
    res = rdr.constraints();
    break;
    
    /*
    std::cout<<"doing the constraint reading"<<std::endl;
    Parse::SMTLIB parser1(*env.options);
  
    string inputFile = env.options->inputFile();
    std::cout<<inputFile<<std::endl;
    istream* input;
    if(inputFile=="") {
      input=&cin;
    } else {
      input=new ifstream(inputFile.c_str());
      if(input->fail()) {
	USER_ERROR("Cannot open problem file: "+inputFile);
      }
    }
  
    parser1.parse(*input);
    std::cout<<parser1.getLispFormula()->toString()<<std::endl;
     */
  }
#endif
  case Options::IS_SMTLIB:
  case Options::IS_SMTLIB2:
  {
    SMTLexer lex(*input);
    SMTParser parser(lex);
    ConstraintReader rdr(parser);
    res = rdr.constraints();

    break;
  }
  case Options::IS_MPS:
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
    while(ite.hasNext())
	std::cout<<ite.next()->toString()<<std::endl;
    throw TimeLimitExceededException();
    ASSERTION_VIOLATION;
#endif 
    break;
  }
  case Options::IS_HUMAN:
    USER_ERROR("human syntax is not supported as input syntax");
  case Options::IS_NETLIB:
 // case Options::IS_SMTLIB2:
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
  ConstraintRCList* constraints = inputConstraints->copy();
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
  case Options::IS_HUMAN:
    outputConstraintInHumanFormat(constraint, out);
    // outputConstraintInSMTFormat(constraint,out);
    return;
  case Options::IS_SMTLIB:
      outputConstraintInSMTFormat(constraint,out);
      return;
  case Options::IS_MPS:
  case Options::IS_NETLIB:
  case Options::IS_SMTLIB2:
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
    if(constraint.freeCoeff().isNegativeAssumingNonzero())
	out<< " " << -constraint.freeCoeff().native() <<" ";
    if(constraint.freeCoeff().isPositiveAssumingNonzero()) 
	out<< " (~ " << constraint.freeCoeff().native() <<")";
  }
    
  while(coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
     if(coeffs.hasNext()) {
	out << " (+ ";
	closedP++;
    }
    if(coeff.value<CoeffNumber::zero()) {
	out << " (* ( ~ " << -coeff.value << " ) " << env.signature->varName(coeff.var) << ")";
    }
    else {
	out <<" (* "<< coeff.value << " " << env.signature->varName(coeff.var) << " )";
    }
   
  }
  
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ )
      out<< "";
  
  while(closedP!=0)
  {
    out<< ")"; 
    closedP--;
    }
   out << " 0 )";
  
 */ 
  Constraint::CoeffIterator coeffs = constraint.coeffs();
  if(!coeffs.hasNext()) {
    out << "0 ";
  }
  while(coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
    if(coeff.value<CoeffNumber::zero()) {
	out << "(" << coeff.value << "*" << env.signature->varName(coeff.var) << ") ";
    }
    else {
	out << coeff.value << "*" << env.signature->varName(coeff.var) << " ";
    }
    if(coeffs.hasNext()) {
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
  if(!coeffs.hasNext()) {
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
    if(constraint.freeCoeff().isNegativeAssumingNonzero())
	out<< " " << -constraint.freeCoeff().native() <<" ";
    if(constraint.freeCoeff().isPositiveAssumingNonzero()) 
	out<< " (~ " << constraint.freeCoeff().native() <<")";
  }
    
  while(coeffs.hasNext()) {
    Constraint::Coeff coeff = coeffs.next();
     if(coeffs.hasNext()) {
	out << " (+ ";
	closedP++;
	 
    }
    
    if(coeff.value<CoeffNumber::zero()) {
	
	out << " (* ( ~ " << -coeff.value << " ) " << env.signature->varName(coeff.var) << ")";
    }
    else {
	out <<" (* "<< coeff.value << " " << env.signature->varName(coeff.var) << " )";
    }
   
  }
  
  if (constraint.freeCoeff() != CoeffNumber::zero() && constraint.type()!= CT_EQ )
      out<< "";
  
  while(closedP!=0)
  {
    out<< ")"; 
    closedP--;
    }
   out << " 0 )";
  
 /* if(constraint.freeCoeff().isNegative() || constraint.freeCoeff() == CoeffNumber::zero() )
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
  case Options::IS_HUMAN:
  {
    ConstraintList::Iterator ite(constraints);
    while(ite.hasNext())
    {
	outputConstraint(*ite.next(), out, syntax);
	out<<endl;
    }
    return;
  }
  case Options::IS_SMTLIB:
  {
     out<<" (benchmark  SOMENAME"<<endl;
    out<<" :source {converted from MIPLIB} "<<endl;
    out<<" :status unknown "<<endl;
    out<<" :category { industrial } "<<endl;
    out<<" :logic QF_LRA "<<endl;
    
    ConstraintList::Iterator fun(constraints);
    std::list<std::string> uni;

    while(fun.hasNext())
    {
	Constraint::CoeffIterator coeffs = fun.next()->coeffs();
	 while(coeffs.hasNext()) {
	     env.signature->varName(coeffs.next().var);
	     uni.push_back(env.signature->varName(coeffs.next().var));
	  //out << ":extrafuns ((" << env.signature->varName(coeffs.next().var) << " Real )) " << endl; 
	}
	
    }

    std::vector<std::string> myvector (uni.begin(),uni.end());
    std::vector<std::string>::iterator ite;
    ite = unique(myvector.begin(),myvector.end());
    myvector.resize( ite - myvector.begin() );
    for (ite=myvector.begin(); ite!=myvector.end(); ++ite)
	out << " " << *ite;
    
    out << ":formula (and "; 
    ConstraintList::Iterator it(constraints);
    while(it.hasNext()) {
      outputConstraint(*it.next(), out, syntax);
      out << " \n";
    }
    
    out<< ") )"<< endl;
    return;
  }
  
  case Options::IS_MPS:
  case Options::IS_NETLIB:
  case Options::IS_SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }
}

void UIHelper::outputAssignment(Assignment& assignemt, ostream& out, Shell::Options::InputSyntax syntax)
{
  CALL("UIHelper::outputAssignment");

  switch(syntax) {
  case Options::IS_HUMAN:
  case Options::IS_MPS:
  case Options::IS_SMTLIB:
  {
    VarIterator vars = assignemt.getAssignedVars();
    while(vars.hasNext()) {
      Var v = vars.next();
      out << env.signature->varName(v) << ": " << assignemt[v] << endl;
    }
    return;
  }
  case Options::IS_NETLIB:
  case Options::IS_SMTLIB2:
    NOT_IMPLEMENTED;
  default:
    ASSERTION_VIOLATION;
  }
}
#endif //GNUMP
}
