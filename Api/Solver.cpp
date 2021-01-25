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
 * @file FormulaBuilder.cpp
 * Implements class FormulaBuilder.
 */

#include "Solver.hpp"

#include "Debug/Assertion.hpp"

#include "Saturation/ProvingHelper.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Map.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Problem.hpp"

#include "Parse/TPTP.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/TPTPPrinter.hpp"



using namespace std;
using namespace Lib;
using namespace Shell;

namespace Api
{


  Solver::Solver(Logic l){
    //switch off all printing
    env.options->setOutputMode(Shell::Options::Output::SMTCOMP);
    //set the time limit to a default of 30. This can be overridden
    env.options->setTimeLimitInSeconds(30);
    preprocessed = false;
    logicSet = false;
    logic = l;
  }

  Solver& Solver::getSolver(Logic l)
  {
    CALL("Solver::getSolver");
    
    static unsigned refCount = 1;
    static Solver solver(l);
   
    if(refCount > 1){
      throw ApiException("Only a single solver object can be in existance at one time");
    }
    
    refCount++;
    return solver;
  }

  void Solver::setLogic(Logic l){
    CALL("Solver::setLogic");

    if(!logicSet){
      logic = l;
    }
  }

  void Solver::resetHard(){
    CALL("Solver::resetHard");

    preprocessed = false;
    logicSet = false;
    fb.reset();
    prob.removeAllFormulas();
    Parse::TPTP::resetAxiomNames();

    delete env.sharing;
    delete env.signature;
    delete env.sorts;
    delete env.statistics;
    if (env.predicateSineLevels) delete env.predicateSineLevels;
    {
      BYPASSING_ALLOCATOR; // use of std::function in options
      delete env.options;
    }

    env.options = new Options;
    env.statistics = new Statistics;  
    env.sorts = new Sorts;
    env.signature = new Signature;
    env.sharing = new Indexing::TermSharing;

    env.options->setOutputMode(Shell::Options::Output::SMTCOMP);
    env.options->setTimeLimitInSeconds(30);
  }

  void Solver::reset(){
    CALL("Solver::reset");

    preprocessed = false;
    prob.removeAllFormulas();
  }

  void Solver::setSaturationAlgorithm(const Lib::vstring& satAlgorithm)
  {
    CALL("Solver::setSaturationAlgorithm");

    if(satAlgorithm == "otter"){
      env.options->setSaturationAlgorithm(Options::SaturationAlgorithm::OTTER);
    } else if(satAlgorithm == "discount"){
      env.options->setSaturationAlgorithm(Options::SaturationAlgorithm::DISCOUNT);
    } else if(satAlgorithm == "lrs"){
      env.options->setSaturationAlgorithm(Options::SaturationAlgorithm::LRS);
    } else if(satAlgorithm == "inst_gen"){
      env.options->setSaturationAlgorithm(Options::SaturationAlgorithm::INST_GEN);
    } else {
      throw ApiException("Unknown saturation algorithm " + satAlgorithm);
    }
  }

  void Solver::setTimeLimit(int timeInSecs)
  {
    CALL("Solver::setTimeLimit");
    
    if(timeInSecs < 1){
      throw ApiException("Cannot set the time limit to " 
                        + Int::toString(timeInSecs) + " since it is < 1");    
    }
    env.options->setTimeLimitInSeconds(timeInSecs);
  }

  void Solver::setOptions(const Lib::vstring optionString)
  {
    CALL("Solver::setOptions");

    env.options->readFromEncodedOptions(optionString);
  }

  Sort Solver::sort(const vstring& sortName)
  {
    CALL("Solver::sort");

    return fb.sort(sortName);
  }

  Sort Solver::integerSort()
  {
    CALL("Solver::integerSort");

    return fb.integerSort();
  }

  Sort Solver::rationalSort()
  {
    CALL("Solver::rationalSort");

    return fb.rationalSort();
  }

  Sort Solver::realSort()
  {
    CALL("Solver::realSort");

    return fb.realSort();
  }

  Sort Solver::defaultSort()
  {
    CALL("Solver::defaultSort");

    return FormulaBuilder::defaultSort();
  }

  Var Solver::var(const vstring& varName)
  {
    CALL("Solver::var");

    return fb.var(varName);
  }

  Var Solver::var(const vstring& varName, Sort varSort)
  {
    CALL("Solver::var");

    return fb.var(varName, varSort);
  }

  Function Solver::function(const vstring& funName,unsigned arity, bool builtIn)
  {
    CALL("Solver::function/2");

    return fb.function(funName, arity, builtIn);
  }

  Function Solver::function(const vstring& funName, unsigned arity, Sort rangeSort, Sort* domainSorts, bool builtIn)
  {
    CALL("Solver::function/4");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(funName[0]) && (funName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Function name must start with a lowercase character or \"$$\"", funName);
      }
      //TODO: add further checks
    }

    return fb.function(funName, arity, rangeSort, domainSorts, builtIn);
  }

  Predicate Solver::predicate(const vstring& predName,unsigned arity, bool builtIn)
  {
    CALL("Solver::predicate/2");

    return fb.predicate(predName, arity, builtIn);
  }

  Predicate Solver::predicate(const vstring& predName, unsigned arity, Sort* domainSorts, bool builtIn)
  {
    CALL("Solver::predicate/3");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(predName[0]) && (predName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Predicate name must start with a lowercase character or \"$$\"", predName);
      }
      //TODO: add further checks
    }
    
    return fb.predicate(predName, arity, domainSorts, builtIn);
  }

  vstring Solver::getSortName(Sort s)
  {
    CALL("Solver::getSortName");

    return fb.getSortName(s);
  }

  vstring Solver::getPredicateName(Predicate p)
  {
    CALL("Solver::getPredicateName");

    return fb.getPredicateName(p);
  }

  vstring Solver::getFunctionName(Function f)
  {
    CALL("Solver::getFunctionName");

    return fb.getFunctionName(f);
  }

  vstring Solver::getVariableName(Var v)
  {
    CALL("Solver::getVariableName");

    return fb.getVariableName(v);
  }

  Term Solver::varTerm(const Var& v)
  {
    CALL("Solver::varTerm");

    return fb.varTerm(v);
  }

  Term Solver::term(const Function& f,const std::vector<Term>& args)
  {
    CALL("Solver::term");

    return fb.term(f, args);
  }

  Formula Solver::atom(const Predicate& p, const std::vector<Term>& args, bool positive)
  {
    CALL("Solver::atom");

    return fb.atom(p, args, positive);
  }

  Formula Solver::equality(const Term& lhs,const Term& rhs, Sort sort, bool positive)
  {
    CALL("Solver::equality/4");

    return fb.equality(lhs, rhs, sort, positive);
  }

  Formula Solver::equality(const Term& lhs,const Term& rhs, bool positive)
  {
    CALL("Solver::equality/3");

    return fb.equality(lhs, rhs, positive);;
  }

  Formula Solver::trueFormula()
  {
    CALL("Solver::trueFormula");

    return fb.trueFormula();
  }

  Formula Solver::falseFormula()
  {
    CALL("Solver::falseFormula");

    return fb.falseFormula();;
  }

  Formula Solver::negation(const Formula& f)
  {
    CALL("Solver::negation");

    return fb.negation(f);
  }

  Formula Solver::formula(Connective c,const Formula& f1,const Formula& f2)
  {
    CALL("Solver::formula(Connective,const Formula&,const Formula&)");

    return fb.formula(static_cast<FormulaBuilder::Connective>(c), f1, f2);
  }

  Formula Solver::formula(Connective q,const Var& v,const Formula& f)
  {
    CALL("Solver::formula(Connective,const Var&,const Formula&)");

    return fb.formula(static_cast<FormulaBuilder::Connective>(q), v, f);
  }

  AnnotatedFormula Solver::annotatedFormula(Formula f, FormulaBuilder::Annotation a, vstring name)
  {
    CALL("Solver::annotatedFormula");

    return fb.annotatedFormula(f, static_cast<FormulaBuilder::Annotation>(a), name);
  }

  Term Solver::term(const Function& c)
  {
    CALL("Solver::term/0");

    return fb.term(c);
  }

  Term Solver::term(const Function& f,const Term& t)
  {
    CALL("Solver::term/1");

    return fb.term(f,t);
  }

  Term Solver::term(const Function& f,const Term& t1,const Term& t2)
  {
    CALL("Solver::term/2");

    return fb.term(f,t1,t2);
  }

  Term Solver::term(const Function& f,const Term& t1,const Term& t2,const Term& t3)
  {
    CALL("Solver::term/3");

    return fb.term(f,t1,t2,t3);
  }

  Term Solver::integerConstant(int i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }

  Term Solver::integerConstant(vstring i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }  

  Term Solver::rationalConstant(Lib::vstring numerator, Lib::vstring denom)
  {
    CALL("Solver::rationalConstant");

    return fb.rationalConstant(numerator, denom);
  }

  Term Solver::realConstant(Lib::vstring r)
  {
    CALL("Solver::realConstant");

    return fb.realConstant(r);
  }

  Term Solver::sum(const Term& t1,const Term& t2)
  {
    CALL("Solver::sum");

    return fb.sum(t1, t2);
  }

  Term Solver::difference(const Term& t1,const Term& t2)
  {
    CALL("Solver::difference");

    return fb.difference(t1, t2);
  }

  Term Solver::multiply(const Term& t1,const Term& t2)
  {
    CALL("Solver::multiply");

    return fb.multiply(t1, t2);
  }

  /*
  Term Solver::divide(const Term& t1,const Term& t2)
  {
    CALL("Solver::divide");

    return fb.divide(t1, t2);
  }*/

  Term Solver::absolute(const Term& t1)
  {
    CALL("absolute::absolute");

    return fb.absolute(t1);
  }

  Term Solver::floor(const Term& t1)
  {
    CALL("Solver::floor");

    return fb.floor(t1);
  }

  Term Solver::ceiling(const Term& t1)
  {
    CALL("Solver::ceiling");

    return fb.ceiling(t1);
  }

  Formula Solver::geq(const Term& t1, const Term& t2)
  {
    CALL("Solver::geq");
 
    return fb.geq(t1, t2);
  }

  Formula Solver::leq(const Term& t1, const Term& t2)
  {
    CALL("Solver::leq");

    return fb.leq(t1, t2);
  }

  Formula Solver::gt(const Term& t1, const Term& t2)
  {
    CALL("Solver::gt");

    return fb.gt(t1, t2);
  }

  Formula Solver::lt(const Term& t1, const Term& t2)
  {
    CALL("Solver::lt");

    return fb.lt(t1, t2);
  }

  Formula Solver::formula(const Predicate& p)
  {
    CALL("Solver::formula/0");

    return fb.formula(p);
  }

  Formula Solver::formula(const Predicate& p,const Term& t)
  {
    CALL("Solver::formula/1");

    return fb.formula(p,t);
  }

  Formula Solver::formula(const Predicate& p,const Term& t1,const Term& t2)
  {
    CALL("Solver::formula/2");

    return fb.formula(p,t1,t2);
  }

  Formula Solver::formula(const Predicate& p,const Term& t1,const Term& t2,const Term& t3)
  {
    CALL("Solver::formula/3");

    return fb.formula(p, t1, t2, t3);
  }

  void Solver::addFormula(Formula f)
  {
    CALL("Solver::addFormula/2");

    if(!preprocessed){
      logicSet = true;
      prob.addFormula(fb.annotatedFormula(f, FormulaBuilder::Annotation::AXIOM));
    } else {
      throw ApiException("A formula cannot be added to a preprocessed problem");
    }
  }

  void Solver::addConjecture(Formula f)
  {
    CALL("Solver::addConjecture");

    if(!preprocessed){
      logicSet = true;
      prob.addFormula(fb.annotatedFormula(f, FormulaBuilder::Annotation::CONJECTURE));
    } else {
      throw ApiException("A conjecture cannot be added to a preprocessed problem");
    }
  }

  void Solver::addFromStream(istream& s, vstring includeDirectory)
  {
    CALL("Solver::addConjecture");
    if(!preprocessed){
      logicSet = true;
      prob.addFromStream(s, includeDirectory, logic == Logic::TPTP);
    } else {
      throw ApiException("Formulas cannot be added to a preprocessed problem");
    }
  }
  
  void Solver::preprocess()
  {
    CALL("Solver::preprocess");

    if(!preprocessed){
      preprocessed = true;
      prob.preprocess();
    }
  }

  Result Solver::solve()
  {
    CALL("Solver::solve");
    
    env.options->setRunningFromApi();
    Kernel::UnitList* units = UnitList::empty();
    AnnotatedFormulaIterator afi = formulas();

    while(afi.hasNext()){
      Kernel::UnitList::push(afi.next(), units);
    }

    Kernel::Problem problem(units);

    if(!preprocessed){
      preprocessed = true;
      Shell::Preprocess prepro(*env.options);
      prepro.preprocess(problem);
    }
  
    Saturation::ProvingHelper::runVampireSaturation(problem, *env.options);
    //To allow multiple calls to solve() for the same problem set.
    Unit::resetFirstNonPreprocessNumber();
    return Result(env.statistics->terminationReason);
  }

  Result Solver::checkEntailed(Formula f)
  {
    CALL("Solver::checkEntailed");
    
    addConjecture(f);
    return solve();
  }

  ///////////////////////////////////////
  // Iterating through the problem

  bool AnnotatedFormulaIterator::hasNext()
  {
    CALL("AnnotatedFormulaIterator::hasNext");

    return current < forms->size();
  }

  AnnotatedFormula AnnotatedFormulaIterator::next()
  {
    CALL("AnnotatedFormulaIterator::next");

    ASS(current < forms->size())
    return (*forms)[current++];
  }

  void AnnotatedFormulaIterator::del()
  {
    CALL("AnnotatedFormulaIterator::del");
    
    if(current != forms->size()){
      (*forms)[current - 1] = forms->top();
    } 
    forms->pop();
  }


  AnnotatedFormulaIterator Solver::formulas()
  {
    CALL("Solver::formulas");

    AnnotatedFormulaIterator res;
    res.current = 0;
    res.forms = &prob.formulas(); 

    return res;
  }

}
