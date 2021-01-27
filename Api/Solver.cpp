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

  Sort Solver::boolSort()
  {
    CALL("Solver::boolSort");

    return FormulaBuilder::boolSort();
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

  Symbol Solver::function(const vstring& funName,unsigned arity, bool builtIn)
  {
    CALL("Solver::function/2");

    std::vector<Sort> domainSorts(arity, defaultSort());
    return fb.symbol(funName, arity, defaultSort(), domainSorts, builtIn);
  }

  Symbol Solver::function(const vstring& funName, unsigned arity, Sort rangeSort, std::vector<Sort>& domainSorts, bool builtIn)
  {
    CALL("Solver::function/4");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(funName[0]) && (funName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Function name must start with a lowercase character or \"$$\"", funName);
      }
      //TODO: add further checks
    }

    return fb.symbol(funName, arity, rangeSort, domainSorts, builtIn);
  }

  Symbol Solver::predicate(const vstring& predName,unsigned arity, bool builtIn)
  {
    CALL("Solver::predicate/2");

    std::vector<Sort> domainSorts(arity, defaultSort());
    return fb.symbol(predName, arity, boolSort(), domainSorts, builtIn);
  }

  Symbol Solver::predicate(const vstring& predName, unsigned arity, std::vector<Sort>& domainSorts, bool builtIn)
  {
    CALL("Solver::predicate/3");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(predName[0]) && (predName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Predicate name must start with a lowercase character or \"$$\"", predName);
      }
      //TODO: add further checks
    }
    
    return fb.symbol(predName, arity, boolSort(), domainSorts, builtIn);
  }

  vstring Solver::getSortName(Sort s)
  {
    CALL("Solver::getSortName");

    return fb.getSortName(s);
  }

  vstring Solver::getSymbolName(Symbol s)
  {
    CALL("Solver::getPredicateName");

    return fb.getSymbolName(s);
  }

  vstring Solver::getVariableName(Var v)
  {
    CALL("Solver::getVariableName");

    return fb.getVariableName(v);
  }

  Expression Solver::varTerm(const Var& v)
  {
    CALL("Solver::varTerm");

    return fb.varTerm(v);
  }

  Expression Solver::term(const Symbol& s,const std::vector<Expression>& args)
  {
    CALL("Solver::term");

    return fb.term(s, args);
  }

  Expression Solver::equality(const Expression& lhs,const Expression& rhs, Sort sort, bool positive)
  {
    CALL("Solver::equality/4");

    return fb.equality(lhs, rhs, sort, positive);
  }

  Expression Solver::equality(const Expression& lhs,const Expression& rhs, bool positive)
  {
    CALL("Solver::equality/3");

    return fb.equality(lhs, rhs, positive);;
  }

  Expression Solver::trueFormula()
  {
    CALL("Solver::trueFormula");

    return fb.trueFormula();
  }

  Expression Solver::falseFormula()
  {
    CALL("Solver::falseFormula");

    return fb.falseFormula();;
  }

  Expression Solver::negation(const Expression& f)
  {
    CALL("Solver::negation");

    return fb.negation(f);
  }

  Expression Solver::andFormula(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::andFormula");

    return fb.andFormula(f1,f2);
  }

  Expression Solver::orFormula(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::orFormula");

    return fb.orFormula(f1,f2);
  }

  Expression Solver::implies(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::implies");

    return fb.implies(f1,f2);
  }

  Expression Solver::iff(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::iff");

    return fb.iff(f1,f2);
  }

  Expression Solver::exor(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::exor");

    return fb.exor(f1,f2);
  }

  Expression Solver::forall(const Var& v,const Expression& f)
  {
    CALL("Solver::forall");

    return fb.forall(v,f);
  }

  Expression Solver::exists(const Var& v,const Expression& f)
  {
    CALL("Solver::exists");

    return fb.exists(v,f);
  }

  Expression Solver::term(const Symbol& s)
  {
    CALL("Solver::term/0");

    return fb.term(s);
  }

  Expression Solver::term(const Symbol& s,const Expression& t)
  {
    CALL("Solver::term/1");

    return fb.term(s,t);
  }

  Expression Solver::term(const Symbol& s,const Expression& t1,const Expression& t2)
  {
    CALL("Solver::term/2");

    return fb.term(s,t1,t2);
  }

  Expression Solver::term(const Symbol& s,const Expression& t1,const Expression& t2,const Expression& t3)
  {
    CALL("Solver::term/3");

    return fb.term(s,t1,t2,t3);
  }

  Expression Solver::integerConstant(int i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }

  Expression Solver::integerConstant(vstring i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }  

  Expression Solver::rationalConstant(Lib::vstring numerator, Lib::vstring denom)
  {
    CALL("Solver::rationalConstant");

    return fb.rationalConstant(numerator, denom);
  }

  Expression Solver::realConstant(Lib::vstring r)
  {
    CALL("Solver::realConstant");

    return fb.realConstant(r);
  }

  Expression Solver::sum(const Expression& t1,const Expression& t2)
  {
    CALL("Solver::sum");

    return fb.sum(t1, t2);
  }

  Expression Solver::difference(const Expression& t1,const Expression& t2)
  {
    CALL("Solver::difference");

    return fb.difference(t1, t2);
  }

  Expression Solver::multiply(const Expression& t1,const Expression& t2)
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

  Expression Solver::absolute(const Expression& t1)
  {
    CALL("absolute::absolute");

    return fb.absolute(t1);
  }

  Expression Solver::floor(const Expression& t1)
  {
    CALL("Solver::floor");

    return fb.floor(t1);
  }

  Expression Solver::ceiling(const Expression& t1)
  {
    CALL("Solver::ceiling");

    return fb.ceiling(t1);
  }

  Expression Solver::geq(const Expression& t1, const Expression& t2)
  {
    CALL("Solver::geq");
 
    return fb.geq(t1, t2);
  }

  Expression Solver::leq(const Expression& t1, const Expression& t2)
  {
    CALL("Solver::leq");

    return fb.leq(t1, t2);
  }

  Expression Solver::gt(const Expression& t1, const Expression& t2)
  {
    CALL("Solver::gt");

    return fb.gt(t1, t2);
  }

  Expression Solver::lt(const Expression& t1, const Expression& t2)
  {
    CALL("Solver::lt");

    return fb.lt(t1, t2);
  }

  void Solver::addFormula(Expression f)
  {
    CALL("Solver::addFormula/2");

    if(!preprocessed){
      logicSet = true;
      prob.addFormula(fb.annotatedFormula(f, FormulaBuilder::Annotation::AXIOM));
    } else {
      throw ApiException("A formula cannot be added to a preprocessed problem");
    }
  }

  void Solver::addConjecture(Expression f)
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
      Shell::Preprocess prepro(*env.options);
      prepro.preprocess(problem);
    }
  
    Saturation::ProvingHelper::runVampireSaturation(problem, *env.options);
    //To allow multiple calls to solve() for the same problem set.
    Unit::resetFirstNonPreprocessNumber();
    return Result(env.statistics->terminationReason);
  }

  Result Solver::checkEntailed(Expression f)
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
      current--;
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
