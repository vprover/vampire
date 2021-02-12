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
 * @file FormulaBuilder.hpp
 * Defines class FormulaBuilder.
 */

#ifndef __API_Solver__
#define __API_Solver__

//#include <ostream>
//#include <climits>

#include "Problem.hpp"
#include "FormulaBuilder.hpp"

//get rid of vstring from this interface somehow
#include <string>

namespace Vampire {

using namespace std;

class AnnotatedFormulaIterator
{
public:
  bool hasNext();
  /**
   * Return the next @b AnnotatedFormula object
   *
   * Each call to the @b next function must be preceded by a call to
   * the @b hasNext function (which has returned @b true).
   */
  AnnotatedFormula next();

  /** delete the last returned formula from the problem */
  void del();
private:
  unsigned current;
  std::vector<AnnotatedFormula>* forms;

  friend class Solver;
};

class Result
{
public:

  bool satisfiable(){
    return _termReason == SATISFIABLE;
  }

  bool unsatisfiable(){
    return _termReason == REFUTATION;
  }

  bool resourcedLimitReached(){
    return (_termReason == RESOURCED_OUT);
  }

private:

  friend class Solver;

  enum TerminationReason {
    SATISFIABLE,
    REFUTATION,
    RESOURCED_OUT
  };

  Result(TerminationReason tr): _termReason(tr) {}

  TerminationReason _termReason;
};


/**
 *  The Solver class is the entry point to Vampire's API.
 *  Notes on this class:
 *  - To get a solver, the getSolver function must be used.
 *  - To set the logic, use the setLogic() function. If the logic 
 *    is not set, it defaults to TPTP which adds constraints to 
 *    variable and symbol names.
 *  - Once a call to preprocess() has been made no further formulas
 *    can be added to the solver.
 *  - Calls to solve() do not modify the solver's formulas. These
 *    remain the formulas originally added to the solver.
 *  - Terms and formulas can be compared using ==, but
 *    this comparison does not NOT take into account variable naming
 *    or commutativity of /\ or \/ or other operators.
 *
 *  A solver can throw the follwing exceptions which must be handled
 *  by the caller:
 *  - Api::ApiException, for general violations of API usage. ApiException
 *    has the following children which can be handled individually if more
 *    detail is required:
 *     - InvalidTPTPNameException
 *     - SortMismatchException
 *     - FormulaBuilderException
 *  - Lib::UserErrorException, thrown at various points during proof search
 *  
 *  To see examples of this class in use, check the vampire/ExamplesApi
 *  folder
 *
 *  The functionality provided by the Term, Formula and Sort classes is
 *  documented in FormulaBuilder.hpp
 */
class Solver
{
public:

  /* The logic. Once a formula has been added to the solver
   * object, its logic cannot be changed 
   */
  //Add different flavours of TPTP and SMTLIB
  enum Logic {
    SMT_LIB = 0,
    TPTP = 1
  };

private:
  Solver(Logic l);

  Solver(Solver const&);         // Don't Implement
  void operator=(Solver const&); // Don't implement

public:

  unsigned getTimeLimit();
  unsigned getElapsedTime();

  static Solver& getSolver(Logic l = TPTP);
  static Solver* getSolverPtr(Logic l = TPTP);

  ~Solver(){}

  /**
   * Create, or retrieve already existing sort with name @c sortName.
   */
  Sort sort(const std::string& sortName);
  /** Return sort for integers */
  Sort integerSort();
  /** Return sort for rationals */
  Sort rationalSort();
  /** Return sort for reals */
  Sort realSort();  
  /** Return array sort */
  Sort arraySort(const Sort& indexSort, const Sort& innerSort);

  /** Sets the logic that the solver works with. After a call to 
   *  addFormula, this function no longer has an effect as the logic
   *  cannot be changed.
   */
  void setLogic(Logic l);

  /*
   * Resets the solver. All formulas are discarded
   * The signature is erased, all options are reset to their defaults
   *
   * WARNING all Term, Formula and Var objects created
   * before a call to reset() are invalid after the call and
   * should not be used! Using them will result in an ApiError
   * being raised.
   */
  void resetHard();

  /*
   * Resets the solver. All formulas are discarded. However,
   * the signature remains, Terms and formula objects continue to be valid
   * and options retain their previous values.
   */
  void reset();
  
  /*
   * Set the saturation algorithm. The options are:
   * - "lrs"
   * - "otter"
   * - "discount"
   * - "inst_gen"
   * Any other value will raise an ApiException. 
   * The argument is case sensitive.
   */
  void setSaturationAlgorithm(const std::string& satAlgorithm);

  /*
   * Set the time limit in seconds that Vampire will run for on a call
   * to solve() or checkEntailed(). The time limit must be greater than
   * 0
   */
  void setTimeLimit(int timeInSecs);

  /*
   * Set the prover options 
   * @param optionString must be in the format of a Vampire encoded 
   * option strings. The format is described ????
   *
   * WARNING this function results in a user error if @param optionString
   * is invalid
   */
  void setOptions(const std::string& optionString);

  /** Prevent the creation of cariables with implicit types.
   *
   *  by default, variables can be created without a type in which 
   *  case, their type is set to a deault type (TPTP $i).
   */
  void disallowImplicitTypingOfVars();

  /**
   * Carry out preprocessing on the currently asserted set of formulas.
   * Notes:
   *  - Preprocessing can only be carried out once.
   *  - After preprocessing has taken place, no formulas can be added.
   * Use formulas() to access the results of preprocessing
   */
  void preprocess();

  /** Attempt to derive a contradiction from the currently asserted set of
   *  formulas.
   *  Notes on usage:
   *  - If problem has not been preprocessed, preprocessing takes place
   *  - The set of formulas is NOT updated by this function a subsequent
   *    call to formulas() will return the originally asserted set.
   */
  Result solve();

  /** Check whether the currently asserted formulas entail f
   */
  Result checkEntailed(Expression f);

  
  /** Get the version of Vampire */
  std::string version();

  /** Get the commit of Vampire library currently being used */
  std::string commit();

  /*
   * Get the default sort (TPTP $i)
   */
  Sort defaultSort();

  /*
   * Get the Boolean sort (TPTP $o)
   */
  Sort boolSort();

  /** Create a variable with the default sort
   * @param varName name of the variable. If the logic is set to TPTP, must be a valid TPTP variable name, 
   * that is, start with a capital-case letter. If the variable name does not conform to TPTP, an exception
   * will be raised.
   */
  Var var(const std::string& varName);

  /** Create a variable
   * @param varName name of the variable. If the logic is set to TPTP, must be a valid TPTP variable name, 
   * that is, start  with a capital-case letter. If the variable name does not conform to TPTP, an exception     
   * will be raised.
   * @param varSort sort of the new variable
   */
  Var var(const std::string& varName, Sort varSort);

  /**
   * Create a function symbol using default sorts. If @b builtIn is true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Symbols of the same name and arity must always have 
   * the same type.
   */
  Symbol function(const std::string& funName, unsigned arity, bool builtIn=false);

  /** Convenience function for creating a symbol with arity 0.
   *  If s is Boolean sort, then a predicate is returned.
   */
  Symbol constantSym(const std::string& name, Sort s);
  /**
   * Create a function symbol with specified range and domain sorts. If @b builtIn is
   * true, the symbol will not be eliminated during preprocessing.
   *
   * @warning Symbols of the same name and arity must have
   * the same type.
   */
  Symbol function(const std::string& funName, unsigned arity, Sort rangeSort, std::vector<Sort>& domainSorts, bool builtIn=false);

  /**
   * Create a predicate symbol using default sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Symbols of the same name and arity must have
   * the same type.
   */
  Symbol predicate(const std::string& predName, unsigned arity, bool builtIn=false);

  /**
   * Create a predicate symbol with specified domain sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Symbols of the same name and arity must have
   * the same type.
   */
  Symbol predicate(const std::string& predName, unsigned arity, std::vector<Sort>& domainSorts, bool builtIn=false);

  /**
   * Return name of the sort @c s.
   */
  std::string getSortName(Sort s);

  /**
   * Return name of the symbol @c s.
   *
   * If the output of dummy names is enabled, the dummy name will be returned here.
   */
  std::string getSymbolName(Symbol s);

  /**
   * Return name of the variable @c v.
   *
   * If the output of dummy names is enabled, the dummy name will be returned here.
   */
  std::string getVariableName(Var v);

  /** build a variable term */
  Expression varTerm(const Var& v);

  /** build a term f(t,ts) 
   *  
   *  NOTE this function can be used to create formulas as well
   *  if @param s is a predicate symbol
   */
  Expression term(const Symbol& s,const std::vector<Expression>& args);

  /** build an equality */
  Expression equality(const Expression& lhs,const Expression& rhs, bool positive=true);

  /** build an equality and check the sorts of the equality sides to be equal to @c sort*/
  Expression equality(const Expression& lhs,const Expression& rhs, Sort sort, bool positive=true);

  /** build either a true or false formula */
  Expression boolFormula(bool value);

  /** build a true formula */
  Expression trueFormula();

  /** build a false formula */
  Expression falseFormula();

  /** build the negation of f. @param f must be of Boolean sort */
  Expression negation(const Expression& f);

  /** build f1 /\ f2. @param f1 and f2 must be of Boolean sort */
  Expression andFormula(const Expression& f1,const Expression& f2);

  /** build f1 \/ f2. @param f1 and f2 must be of Boolean sort */
  Expression orFormula(const Expression& f1,const Expression& f2);

  /** build f1 -> f2. @param f1 and f2 must be of Boolean sort */
  Expression implies(const Expression& f1,const Expression& f2);

  /** build f1 <-> f2. @param f1 and f2 must be of Boolean sort */
  Expression iff(const Expression& f1,const Expression& f2);

  /** build f1 XOR f2. @param f1 and f2 must be of Boolean sort */
  Expression exor(const Expression& f1,const Expression& f2);

  /** build quantified formula (q v)f. @param f must be of Boolean sort */
  Expression forall(const Var& v,const Expression& f);

  /** build quantified formula (q v)f. @param f must be of Boolean sort */
  Expression exists(const Var& v,const Expression& f);

  // Special cases, convenient to have

  /** build a constant term (or formula) c */
  Expression term(const Symbol& c);

  /** build a constant term (or formula) with name @param name 
   *  sort @param s
   */
  Expression constant(const std::string& name, Sort s);

  /** build a unary term (or formula) f(t) */
  Expression term(const Symbol& f,const Expression& t);

  /** build a binary term (or formula) f(t1,t2) */
  Expression term(const Symbol& f,const Expression& t1,const Expression& t2);

  /** build a term (or formula) f(t1,t2,t3) */
  Expression term(const Symbol& f,const Expression& t1,const Expression& t2,const Expression& t3);

  /** Build a conditional: if cond then t1 else t2 
   *  @param cond must be of Boolean sort
   *  @param t1 and @param t2 must have the same sort
   */
  Expression ite(const Expression& cond,const Expression& t1,const Expression& t2); 

  /** Return constant representing @c i */
  Expression integerConstant(int i);
  
  /**
   * Return constant representing @c i
   *
   * @c FormulaBuilderException may be thrown if @c i is not a proper value, or too large
   * for Vampire internal representation.
   */
  Expression integerConstant(std::string i);

  /** Return a rational constant representing @c numerator/ @c denom */
  Expression rationalConstant(std::string numerator, std::string denom);

  /** Return a rational constant  
   *  @param r must be of the form numerator/denom
   *  otherwise an exception is thrown.
   */
  Expression rationalConstant(std::string r);

  /** Return a real constant representing @c i */
  Expression realConstant(std::string r);

  /** Create the term t1 + t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Expression sum(const Expression& t1,const Expression& t2);

  /** Create the term t1 - t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Expression difference(const Expression& t1,const Expression& t2);

  /** Create the term t1 x t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Expression multiply(const Expression& t1,const Expression& t2);

  /** Create the term t1 / t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Expression div(const Expression& t1,const Expression& t2);

  /** Create the term t1 mod t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Expression mod(const Expression& t1,const Expression& t2);

  /** Create the term -t
   *  t must be of integer, real or rational sort.
   */
  Expression neg(const Expression& t);

  /* Converts t from integer sort to real sort.
   * t must be of integer sort
   */
  Expression int2real(const Expression& t);

  /* Converts t from real sort to integer sort.
   * t must be of real sort
   */
  Expression real2int(const Expression& t);

  /** create the floor of @param t1 which must be of integer rational or real sort */
  Expression floor(const Expression& t1);

  /** create the ceiling of @param t1 which must be of integer rational or real sort */
  Expression ceiling(const Expression& t1);

  /** build  | t1 |. t1 must be of integer sort */
  Expression absolute(const Expression& t1);

  /** build the formula t1 >= t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Expression geq(const Expression& t1, const Expression& t2);

  /** build the formula t1 <= t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Expression leq(const Expression& t1, const Expression& t2);

  /** build the formula t1 > t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Expression gt(const Expression& t1, const Expression& t2);

  /** build the formula t1 < t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Expression lt(const Expression& t1, const Expression& t2);


  /*******************************************************/
  /*                Array operations                     */
  /*******************************************************/

  /**
   *  Build the term store(array, index, newVal)
   *  @param array must be of array sort
   *  @param index must have the same sort as the index sort of @array
   *  @param newVal must have the same sort as the inner sort of @array
   */
  Expression store(const Expression& array, const Expression& index, const Expression& newVal);

  /**
   *  Build the term select(array, index)
   *  @param array must be of array sort
   *  @param index must have the same sort as the index sort of @array
   */
  Expression select(const Expression& array, const Expression& index);


  /**
   * Add an axiom into the problem
   */
  void addFormula(Expression f);

  /**
   * Add an assumption into the problem
   */
  void assertFormula(Expression f){ addFormula(f); }

  /** 
    * Add a conjecture to the problem
    */
  void addConjecture(Expression f);
  
  /**
   * Add formulas parsed from a stream
   *
   * @param s the stream
   * @param includeDirectory where the parser will look for included files
   *
   * WARNING it is assumed that the syntax of the stream matches the logic
   * of the solver
   */
  void addFromStream(istream& s, std::string includeDirectory="./"); 
  
  /**
   * Return iterator of formulas in the problem
   *
   * When the problem is modified, behavior of all existing iterators
   * (except for the one that caused the modification) is undefined.
   */
  AnnotatedFormulaIterator formulas();

  /**
   * Return number of formulas currently asserted
   */
  size_t size();

  /**
   * Return true if no formulas are currently asserted in the solver
   */
  bool empty();

private:
  FormulaBuilder fb;
  Problem prob;
  Logic logic;
  bool logicSet;
  int timeLimit;
  bool preprocessed;
};




}

#endif // __API_Solver__
