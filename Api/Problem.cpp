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
 * @file Api/Problem.cpp
 * Implements class Problem.
 */

#include "Problem.hpp"

#include "Helper_Internal.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"
#include "Lib/List.hpp"
#include "Lib/StringUtils.hpp"

#include "Lib/StringUtils.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Problem.hpp"

#include "Shell/CNF.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/Naming.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/SineUtils.hpp"
#include "Shell/FOOLElimination.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/VarManager.hpp"

#include "Parse/TPTP.hpp"
#include "Parse/SMTLIB2.hpp"

namespace Vampire {

//using namespace Lib;

Problem::Problem()
{
  CALL("Problem::Problem");
}

Problem::~Problem()
{
  CALL("Problem::~Problem");
}

void Problem::addFormula(AnnotatedFormula f)
{
  CALL("Problem::addFormula");
  
  _formulas.push_back(f);
}

size_t Problem::size()
{
  CALL("Problem::size");
  
  return _formulas.size();
}

bool Problem::empty()
{
  CALL("Problem::empty");

  return size()==0;
}



///////////////////////////////////////
// Parsing

void Problem::addFromStream(istream& s, string includeDirectory, bool tptp)
{
  CALL("Problem::addFromStream");

  using namespace Shell;

  vstring originalInclude=env.options->include();
  env.options->setInclude(StringUtils::copy2vstr(includeDirectory));

  Kernel::UnitList* units;

  if(tptp){
    Parse::TPTP parser(s);
    try{
      parser.parse();
    }
    catch (UserErrorException& exception) {
      vstring msg = exception.msg();
      throw Parse::TPTP::ParseErrorException(msg,parser.lineNumber());
    }
    units = parser.units();
    UIHelper::setHavingConjecture(parser.containsConjecture());
  } else {
    Parse::SMTLIB2 parser(*env.options);
    parser.parse(s);
          Unit::onParsingEnd();

    units = parser.getFormulas();
    //In a normal parse the th eline below is used to set the SMTLIB logic
    //Is it important?
    //smtLibLogic = parser.getLogic();
    UIHelper::setHavingConjecture(false);
  }

  env.options->setInclude(originalInclude);
  while(units) {
    Kernel::Unit* u=Kernel::UnitList::pop(units);
    addFormula(AnnotatedFormula(u));
  }
}

///////////////////////////////////////
// Clausification

void outputAttributes(ostream& out, FBHelperCore::AttribStack* attribs)
{
  CALL("outputAttributes");

  if(!attribs) {
    return;
  }
  FBHelperCore::AttribStack::BottomFirstIterator it(*attribs);
  while(it.hasNext()) {
    FBHelperCore::AttribPair attr = it.next();
    out << " | $attr(" << attr.first << ", " << attr.second <<")";
  }
}

/*void outputSymbolTypeDefinitions(ostream& out, unsigned symNumber, bool function, bool outputAllTypeDefs,
    FBHelperCore::AttribStack* attribs, bool dummyNames)
{
  CALL("outputSymbolTypeDefinitions");

  Signature::Symbol* sym = function ?
      env.signature->getFunction(symNumber) : env.signature->getPredicate(symNumber);

  if(sym->interpreted()) {
    //there is no need to output type definitions for interpreted symbols
    return;
  }

  OperatorType* type = function ? sym->fnType() : sym->predType();

  if(!outputAllTypeDefs && type->isAllDefault()) {
    return;
  }

  vstring symName = dummyNames ? (DefaultHelperCore::getDummyName(!function, symNumber)) : sym->name();

  out << "tff(" << (function ? "func" : "pred") << "_def_" << symNumber << ",type, "
      << symName << ": ";

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
  outputAttributes(out, attribs);
  out << " )." << endl;

}

void Problem::outputTypeDefinitions(ostream& out, bool outputAllTypeDefs)
{
  CALL("Problem::outputTypeDefinitions");

  DefaultHelperCore* core0 = _data->getCore();
  bool dummyNames = core0 && core0->outputDummyNames();
  FBHelperCore* core = (core0 && core0->isFBHelper()) ? static_cast<FBHelperCore*>(core0) : 0;
  unsigned sorts = env.sorts->count();
  for(unsigned i=Sorts::FIRST_USER_SORT; i<sorts; i++) {
    out << "tff(sort_def_" << i << ",type, " << env.sorts->sortName(i) << ": $tType";
    if(core) { outputAttributes(out, &core->getSortAttributes(i)); }
    out << " )." << endl;
  }


  unsigned funs = env.signature->functions();
  for(unsigned i=0; i<funs; i++) {
    outputSymbolTypeDefinitions(out, i, true, outputAllTypeDefs,
	core ? &core->getFunctionAttributes(i) : 0, dummyNames);
  }
  unsigned preds = env.signature->predicates();
  for(unsigned i=1; i<preds; i++) {
    outputSymbolTypeDefinitions(out, i, false, outputAllTypeDefs,
	core ? &core->getPredicateAttributes(i) : 0, dummyNames);
  }
}

void Problem::output(ostream& out, bool outputTypeDefs, bool outputAllTypeDefs)
{
  CALL("Problem::output");

  if(outputTypeDefs) {
    outputTypeDefinitions(out, outputAllTypeDefs);
  }
  AnnotatedFormulaIterator afit = formulas();
  while(afit.hasNext()) {
    out<<afit.next()<<endl;
  }
}*/

void Problem::preprocess()
{
  CALL("Problem::preprocess");
  
  Kernel::UnitList* units = UnitList::empty();

  while(!_formulas.empty()){
    AnnotatedFormula f = _formulas.back();
    _formulas.pop_back();
    Kernel::UnitList::push(f.unit, units);
  }

  Kernel::Problem problem(units);
  Shell::Preprocess prepro(*env.options);
  prepro.preprocess(problem);

  units = problem.units();
  while(units){
    _formulas.push_back(AnnotatedFormula(units->head()));
    units = units->tail();
  }
}

void Problem::removeAllFormulas()
{
  CALL("Problem::removeAllFormulas");

  _formulas.clear();
}


void Problem::outputStatistics(ostream& out)
{
  CALL("Problem::outputStatictics");

  env.statistics->print(out);
}


} // namespace Api
