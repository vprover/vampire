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
#include "Lib/StringUtils.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Sys/Multiprocessing.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Problem.hpp"

#include "CASC/PortfolioMode.hpp"

#include "Parse/TPTP.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/Statistics.hpp"

#include <unistd.h>
#include <fcntl.h>

using namespace std;
using namespace Lib;
using namespace Shell;

namespace Vampire
{

  unsigned Solver::getTimeLimit() {
    return env.options->timeLimitInDeciseconds();
  }

  unsigned Solver::getElapsedTime(){
    return env.timer->elapsedDeciseconds();
  }

  Solver::Solver(Logic l){
    //switch off all printing
    env.options->setOutputMode(Shell::Options::Output::API);
    preprocessed = false;
    logicSet = false;
    verbose = false;
    timeLimit = 0;
    logic = l;
    env.options->setTimeLimitInSeconds(0);
  }

  Solver& Solver::getSolver(Logic l)
  {
    CALL("Solver::getSolver");

    static Solver solver(l);  
    static unsigned refCount = 1;

    if(refCount > 1){
      throw ApiException("Only a single solver object can be in existance at one time");
    }
    
    refCount++;
    return solver;
  }

  Solver* Solver::getSolverPtr(Logic l)
  {
    CALL("Solver::getSolverPtr");

    return &getSolver(l);
  }


  void Solver::setLogic(Logic l){
    CALL("Solver::setLogic");

    if(!logicSet){
      logic = l;
    }
  }

  void Solver::setVerbose(){
    CALL("Solver::setVerbose");

    verbose = true;
  }

  void Solver::resetHard(){
    CALL("Solver::resetHard");

    preprocessed = false;
    logicSet = false;
    verbose = false;
    fb.reset();
    prob.removeAllFormulas();
    Parse::TPTP::resetAxiomNames();

    delete env.sharing;
    delete env.signature;
    delete env.statistics;
    if (env.predicateSineLevels) delete env.predicateSineLevels;
    {
      BYPASSING_ALLOCATOR; // use of std::function in options
      delete env.options;
    }

    env.options = new Options;
    env.statistics = new Statistics;  
    env.signature = new Signature;
    env.sharing = new Indexing::TermSharing;

    timeLimit = 0;

    env.options->setOutputMode(Shell::Options::Output::API);
    env.options->setTimeLimitInSeconds(0);
  }

  void Solver::reset(){
    CALL("Solver::reset");

    preprocessed = false;
    prob.removeAllFormulas();
  }

  void Solver::setSaturationAlgorithm(const string& satAlgorithm)
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
                        + to_string(timeInSecs) + " since it is < 1");    
    }
    timeLimit = timeInSecs;
  }

  void Solver::setOptions(const string& optionString)
  {
    CALL("Solver::setOptions");

    env.options->readFromEncodedOptions(StringUtils::copy2vstr(optionString));
  }

  void Solver::setOption(const std::string& optName, const std::string& optValue)
  {
    CALL("Solver::useMultiClauseInduction");
    
    try{
      auto optNameStr = StringUtils::copy2vstr(optName);
      auto optValueStr = StringUtils::copy2vstr(optValue);
      env.options->set(optNameStr, optValueStr);
    }catch(Lib::UserErrorException& e){
      // should make this more robust
      // what about if the error messages change?
      if(e.msg().find("is an invalid value") != std::string::npos){
        cout << "WARNING: " + optValue + " is not a valid value for option " + optName + ". Ignoring request to set option.\n" << endl;
      } else if(e.msg().find("not a valid option") != std::string::npos){
        cout << "WARNING: " + optName + "is not a valid option. Ignoring request to set.\n" << endl;         
      } else {
        throw ApiException("Unexpected user error when attempting to set option with message: " + 
          StringUtils::copy2str(e.msg()));
      }
    }
  }

  void Solver::forceOptions(const std::string& optString)
  {
    CALL("Solver::forceOptions");

    try{
      env.options->set("forced_options", StringUtils::copy2vstr(optString));
    }catch(Lib::UserErrorException& e){
      // TODO improve error handling here
      cout << "WARNING: failed to force options " + e.msg() << endl;
    }    
  }

  Sort Solver::sort(const string& sortName)
  {
    CALL("Solver::sort");
   
    std::string name = sortName;
    if(logic == SMT_LIB){
      // at the moment we only support arity 0 sorts ...
      name = sortName + "()";
    }

    return fb.sort(name);
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

  std::string Solver::version()
  {
    CALL("Solver::version");

    string str =  VERSION_STRING;
    return str.substr(8,5);
  }

  std::string Solver::commit()
  {
    CALL("Solver::commit");

    string str =  VERSION_STRING;
    return str.substr(23,7);
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

  Sort Solver::arraySort(const Sort& indexSort, const Sort& innerSort)
  {
    CALL("Solver::arraySort");

    return fb.arraySort(indexSort, innerSort);
  }


  Var Solver::var(const string& varName)
  {
    CALL("Solver::var");

    if(fb.checkNames() && logic == TPTP ) {
      if(!isupper(varName[0])) {
        throw InvalidTPTPNameException("Variable name must start with an uppercase character when using TPTP syntax", 
                                      varName);
      }
      //TODO: add further checks
    }

    return fb.var(varName);
  }

  Var Solver::var(const string& varName, Sort varSort)
  {
    CALL("Solver::var");

    if(fb.checkNames() && logic == TPTP ) {
      if(!isupper(varName[0])) {
        throw InvalidTPTPNameException("Variable name must start with an uppercase character when using TPTP syntax", 
                                        varName);
      }
      //TODO: add further checks
    }

    return fb.var(varName, varSort);
  }

  Symbol Solver::constantSym(const std::string& name, Sort s)
  {
    CALL("Solver::constantSym");

    if(s == boolSort()){
      return predicate(name, 0);
    } else {
      std::vector<Sort> emptyVec;
      return function(name, 0, s, emptyVec);
    }
  }


  Symbol Solver::function(const string& funName,unsigned arity, bool builtIn)
  {
    CALL("Solver::function/2");

    std::vector<Sort> domainSorts(arity, defaultSort());
    return fb.symbol(funName, arity, defaultSort(), domainSorts, RapidSym::NONE, builtIn);
  }

  Symbol Solver::function(const string& funName, unsigned arity, Sort rangeSort, 
    std::vector<Sort>& domainSorts, RapidSym rs, bool builtIn)
  {
    CALL("Solver::function/4");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(funName[0]) && (funName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Function name must start with a lowercase character or \"$$\"", funName);
      }
      //TODO: add further checks
    }

    return fb.symbol(funName, arity, rangeSort, domainSorts, rs, builtIn);
  }

  Symbol Solver::predicate(const string& predName,unsigned arity, bool builtIn)
  {
    CALL("Solver::predicate/2");

    std::vector<Sort> domainSorts(arity, defaultSort());
    return fb.symbol(predName, arity, boolSort(), domainSorts, RapidSym::NONE, builtIn);
  }

  Symbol Solver::predicate(const string& predName, unsigned arity, std::vector<Sort>& domainSorts, 
                           RapidSym rs, bool builtIn)
  {
    CALL("Solver::predicate/3");

    //TOTO add checks for SMT as well
    if(fb.checkNames() && logic == TPTP) {
      if(!islower(predName[0]) && (predName.substr(0,2)!="$$")) {
        throw InvalidTPTPNameException("Predicate name must start with a lowercase character or \"$$\"", predName);
      }
      //TODO: add further checks
    }
    
    return fb.symbol(predName, arity, boolSort(), domainSorts, rs, builtIn);
  }

  string Solver::getSortName(Sort s)
  {
    CALL("Solver::getSortName");

    return fb.getSortName(s);
  }

  string Solver::getSymbolName(Symbol s)
  {
    CALL("Solver::getPredicateName");

    return fb.getSymbolName(s);
  }

  string Solver::getVariableName(Var v)
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

  Expression Solver::boolFormula(bool value)
  {
    CALL("Solver::boolFormula");

    return value ? trueFormula() : falseFormula();
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

  Expression Solver::andFormula(const std::vector<Expression>& conjuncts)
  {
    CALL("Solver::andFormula");

    return fb.andFormula(conjuncts);   
  }

  Expression Solver::orFormula(const Expression& f1,const Expression& f2)
  {
    CALL("Solver::orFormula");

    return fb.orFormula(f1,f2);
  }

  Expression Solver::orFormula(const std::vector<Expression>& disjuncts)
  {
    CALL("Solver::orFormula");

    return fb.orFormula(disjuncts);
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

  Expression Solver::constant(const std::string& name, Sort s)
  {
    CALL("Solver::constant");

    return term(constantSym(name, s));
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

  Expression Solver::ite(const Expression& cond,const Expression& t1,const Expression& t2)
  {
    CALL("Solver::ite");

    return fb.ite(cond, t1, t2);
  }

  Expression Solver::integerConstant(int i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }

  Expression Solver::integerConstant(string i)
  {
    CALL("Solver::integerConstant");

    return fb.integerConstantTerm(i);
  }  

  Expression Solver::rationalConstant(string numerator, string denom)
  {
    CALL("Solver::rationalConstant");

    return rationalConstant(numerator + "/" + denom);
  }

  Expression Solver::rationalConstant(string r)
  {
    CALL("Solver::rationalConstant/2");

    std::size_t found = r.find("/");
    if(found == std::string::npos){
      throw ApiException("Cannot form a rational constant from " + r + " as it is not of the form a/b");  
    }
    return fb.rationalConstant(r);
  }

  Expression Solver::realConstant(string r)
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

  Expression Solver::div(const Expression& t1,const Expression& t2)
  {
    CALL("Solver::divide");

    return fb.div(t1, t2);
  }

  Expression Solver::mod(const Expression& t1,const Expression& t2)
  {
    CALL("Solver::divide");

    return fb.mod(t1, t2);
  }

  Expression Solver::neg(const Expression& t)
  {
    CALL("Solver::divide");

    return fb.neg(t);
  }

  Expression Solver::int2real(const Expression& t)
  {
    CALL("Solver::int2real");

    return fb.int2real(t);
  }

  Expression Solver::real2int(const Expression& t)
  {
    CALL("Solver::real2int");

    return fb.real2int(t);
  }

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

  Expression Solver::store(const Expression& array, const Expression& index, const Expression& newVal)
  {
    CALL("Solver::store");

    return fb.store(array, index, newVal);
  }

  Expression Solver::select(const Expression& array, const Expression& index)
  {
    CALL("Solver::select");

    return fb.select(array, index);
  }


  void Solver::addFormula(Expression f)
  {
    CALL("Solver::addFormula/2");

    if(!preprocessed){
      logicSet = true;
      // always axiom at the moment, to ensure different to theory axioms
      prob.addFormula(fb.annotatedFormula(f, FormulaBuilder::Annotation::ASSUMPTION));
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

  void Solver::addFromStream(istream& s, string includeDirectory)
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
    
    return solveImpl();
  }

  Result Solver::solveWithCasc()
  {
    CALL("Solver::solveWithCasc");
    
    if(preprocessed){
      throw ApiException("Cannot run CASC mode on an already processed problem");      
    }
    
    env.options->setMode(Options::Mode::CASC);
    return solveImpl(true);
  }

  Result Solver::solveWithSched(Schedule sched)
  {
    CALL("Solver::solveWithSched");

    if(preprocessed){
      throw ApiException("Cannot run portfolio mode on an already processed problem");      
    }

    switch(sched){
      case Schedule::RAPID:
        env.options->setSchedule(Options::Schedule::RAPID);
        break;
      case Schedule::RAPID_INDUCT:
        env.options->setSchedule(Options::Schedule::RAPID_INDUCTION);
        break; 
      case Schedule::NONE:
        // TODO look into how to output warnings
        std::cout << "WARNING: Trying to run in portfolio mode without setting a schedule. Defaulting to CASC" << std::endl;  
        // deliberately no break here
      case Schedule::CASC:
        // do nothing, CASC is default schedule
        break;
    }

    env.options->setMode(Options::Mode::PORTFOLIO);
    return solveImpl(true);
  }

  #define READ 0
  #define WRITE 1

  Result Solver::solveImpl(bool portfolioMode)
  {
    CALL("Solver::solveImpl");

    if(!timeLimit){
      env.options->setTimeLimitInSeconds(30);
    } else {
      env.options->setTimeLimitInSeconds(timeLimit);      
    }

    Allocator::setMemoryLimit(env.options->memoryLimit() * 1048576ul);   

    env.options->setRunningFromApi();
    if(verbose)
      env.options->setOutputMode(Options::Output::SZS);

    //env.options->set("show_new", "on");
    //env.options->set("show_preprocessing", "on");    

    int fd[2];
    int ret = pipe(fd);
    ASS_NEQ(ret, -1);

    // set non-blocking in case child is not able to write to pipe for
    // some reason (e.g. timeout)
    ret = fcntl(fd[READ], F_SETFL, fcntl(fd[READ], F_GETFL) | O_NONBLOCK);
    ASS_NEQ(ret, -1);

    pid_t pid = Multiprocessing::instance()->fork();
    ASS_NEQ(pid, -1);

    if(pid)
    { //parent
      close(fd[WRITE]);
      int res;
      // goto sleep and let child do its thing
      Multiprocessing::instance()->waitForChildTermination(res);

      Shell::Statistics::TerminationReason r = 
          Shell::Statistics::TerminationReason::UNKNOWN;

      read(fd[READ],&r,sizeof(r));
      close(fd[READ]);

      Result::TerminationReason tr;
      if(r == Shell::Statistics::REFUTATION){
        tr = Result::REFUTATION;
      } else 
      if(r == Shell::Statistics::SATISFIABLE){
        tr = Result::SATISFIABLE;
      } else {
        //catch all
        tr = Result::RESOURCED_OUT;
      }

      return Result(tr);   

    } else {
      // child
      close(fd[READ]);
      
      Kernel::UnitList* units = UnitList::empty();
      AnnotatedFormulaIterator afi = formulas();

      while(afi.hasNext()){
        Kernel::UnitList::push(afi.next(), units);
      }

      env.timer->start();

      if(portfolioMode){
        Kernel::Problem* prob = new Kernel::Problem(units);
        CASC::PortfolioMode::perform(env.options->slowness(), prob, fd);
      } else {
        Kernel::Problem problem(units);

        if(!preprocessed){
          Shell::Preprocess prepro(*env.options);
          prepro.preprocess(problem);
        }      
        Saturation::ProvingHelper::runVampireSaturation(problem, *env.options, fd);      
      }
    }
    assert(false);
  }

  Result Solver::checkEntailed(Expression f)
  {
    CALL("Solver::checkEntailed");
    
    addConjecture(f);
    return solve();
  }

  bool Solver::empty()
  {
    CALL("Solver::empty");

    return prob.empty();
  }

  // TODO at the moment we ignore the fileName parameter
  // Also, the problem created is not in TPTP format
  void Solver::outputProblem(std::string fileName)
  {
    CALL("Solver::outputProblem");

    prob.output(std::cout);
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
      (*forms)[current - 1] = forms->back();
      current--;
    } 
    forms->pop_back();
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
