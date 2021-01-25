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

#include <ostream>
#include <climits>

#include "Problem.hpp"
#include "FormulaBuilder.hpp"

#include "Shell/Statistics.hpp"

#include "Lib/VString.hpp"

namespace Api {

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
  Problem::AnnotatedFormulaStack* forms;

  friend class Solver;
};

class Result
{
public:

  Result(Shell::Statistics::TerminationReason tr){
    _termReason = tr;
  }

  bool satisfiable(){
    return _termReason == Shell::Statistics::SATISFIABLE;
  }

  bool unsatisfiable(){
    return _termReason == Shell::Statistics::REFUTATION;
  }

  bool resourcedLimitReached(){
    return (_termReason == Shell::Statistics::TIME_LIMIT ||
            _termReason == Shell::Statistics::MEMORY_LIMIT);
  }

private:

  Shell::Statistics::TerminationReason _termReason;
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
 */
class Solver
{
public:

  /* The logic. Once a formula has been added to the solver
   * object, its logic cannot be changed 
   */
  //Add different flavours of TPTP and SMTLIB
  enum Logic {
    SMT_LIB,
    TPTP
  };

private:
  Solver(Logic l);

  Solver(Solver const&);         // Don't Implement
  void operator=(Solver const&); // Don't implement

public:

  static Solver& getSolver(Logic l = TPTP);

  enum Connective {
    TRUE,
    FALSE,
    ATOM,
    AND,
    OR,
    IMP,
    IFF,
    XOR,
    NOT,
    FORALL,
    EXISTS,
    /** if-then-else connective */
    ITE
  };

  ~Solver(){}

  /**
   * Create, or retrieve already existing sort with name @c sortName.
   */
  Sort sort(const Lib::vstring& sortName);
  /** Return sort for integers */
  Sort integerSort();
  /** Return sort for rationals */
  Sort rationalSort();
  /** Return sort for reals */
  Sort realSort();  
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
  void setSaturationAlgorithm(const Lib::vstring& satAlgorithm);

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
  void setOptions(const Lib::vstring optionString);

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
  Result checkEntailed(Formula f);

  /*
   * Get the default sort (TPTP $i)
   */
  Sort defaultSort();

  /** Create a variable with the default sort
   * @param varName name of the variable. If the logic is set to TPTP, must be a valid TPTP variable name, 
   * that is, start with a capital-case letter. If the variable name does not conform to TPTP, an exception
   * will be raised.
   */
  Var var(const Lib::vstring& varName);

  /** Create a variable
   * @param varName name of the variable. If the logic is set to TPTP, must be a valid TPTP variable name, 
   * that is, start  with a capital-case letter. If the variable name does not conform to TPTP, an exception     
   * will be raised.
   * @param varSort sort of the new variable
   */
  Var var(const Lib::vstring& varName, Sort varSort);

  /**
   * Create a function symbol using default sorts. If @b builtIn is true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Functions of the same name and arity must always have 
   * the same type.
   */
  Function function(const Lib::vstring& funName, unsigned arity, bool builtIn=false);

  /**
   * Create a function symbol with specified range and domain sorts. If @b builtIn is
   * true, the symbol will not be eliminated during preprocessing.
   *
   * @warning Functions of the same name and arity must have
   * the same type.
   */
  //Change to use std::vector ?
  Function function(const Lib::vstring& funName, unsigned arity, Sort rangeSort, Sort* domainSorts, bool builtIn=false);

  /**
   * Create a predicate symbol using default sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Predicates of the same name and arity must have
   * the same type.
   */
  Predicate predicate(const Lib::vstring& predName, unsigned arity, bool builtIn=false);

  /**
   * Create a predicate symbol with specified domain sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Predicates of the same name and arity must have
   * the same type.
   */
  //Change to use std::vector ?
  Predicate predicate(const Lib::vstring& predName, unsigned arity, Sort* domainSorts, bool builtIn=false);

  /**
   * Return name of the sort @c s.
   */
  Lib::vstring getSortName(Sort s);

  /**
   * Return name of the predicate @c p.
   *
   * If the output of dummy names is enabled, the dummy name will be returned here.
   */
  Lib::vstring getPredicateName(Predicate p);

  /**
   * Return name of the function @c f.
   *
   * If the output of dummy names is enabled, the dummy name will be returned here.
   */
  Lib::vstring getFunctionName(Function f);

  /**
   * Return name of the variable @c v.
   *
   * If the output of dummy names is enabled, the dummy name will be returned here.
   */
  Lib::vstring getVariableName(Var v);

  /** build a variable term */
  Term varTerm(const Var& v);

  /** build a term f(t,ts) */
  Term term(const Function& f,const std::vector<Term>& args);

  /** build an atomic formula different from equality */ 
  Formula atom(const Predicate& p, const std::vector<Term>& args, bool positive=true);

  /** build an equality */
  Formula equality(const Term& lhs,const Term& rhs, bool positive=true);

  /** build an equality and check the sorts of the equality sides to be equal to @c sort*/
  Formula equality(const Term& lhs,const Term& rhs, Sort sort, bool positive=true);

  /** build a true formula */
  Formula trueFormula();

  /** build a false formula */
  Formula falseFormula();

  /** build the negation of f */
  Formula negation(const Formula& f);

  /** build f1 c f2 */
  Formula formula(Connective c,const Formula& f1,const Formula& f2);

  /** build quantified formula (q v)f */
  Formula formula(Connective q,const Var& v,const Formula& f);

  // Special cases, convenient to have

  /** build a constant term c */
  Term term(const Function& c);

  /** build a unary term f(t) */
  Term term(const Function& f,const Term& t);

  /** build a binary term f(t1,t2) */
  Term term(const Function& f,const Term& t1,const Term& t2);

  /** build a term f(t1,t2,t3) */
  Term term(const Function& f,const Term& t1,const Term& t2,const Term& t3);

  /** Return constant representing @c i */
  Term integerConstant(int i);
  
  /**
   * Return constant representing @c i
   *
   * @c FormulaBuilderException may be thrown if @c i is not a proper value, or too large
   * for Vampire internal representation.
   */
  Term integerConstant(Lib::vstring i);

  /** Return a rationa constant representing @c numerator/ @c denom */
  Term rationalConstant(Lib::vstring numerator, Lib::vstring denom);

  /** Return a real constant representing @c i */
  Term realConstant(Lib::vstring r);

  /** Create the term t1 + t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Term sum(const Term& t1,const Term& t2);

  /** Create the term t1 - t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Term difference(const Term& t1,const Term& t2);

  /** Create the term t1 x t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Term multiply(const Term& t1,const Term& t2);

  /** Create the term t1 / t2 
   *  Both t1 and t2 must be of the same type
   *  which must be either integer, real or rational.
   */
  Term divide(const Term& t1,const Term& t2);

  /** create the floor of @param t1 which must be of integer rational or real sort */
  Term floor(const Term& t1);

  /** create the ceiling of @param t1 which must be of integer rational or real sort */
  Term ceiling(const Term& t1);

  /** build  | t1 |. t1 must be of integer sort */
  Term absolute(const Term& t1);

  /** build the formula t1 >= t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Formula geq(const Term& t1, const Term& t2);

  /** build the formula t1 <= t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Formula leq(const Term& t1, const Term& t2);

  /** build the formula t1 > t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Formula gt(const Term& t1, const Term& t2);

  /** build the formula t1 < t2 
   *  t1 and t2 must be of the same type and their type must be
   *  integer, rational or real
   */
  Formula lt(const Term& t1, const Term& t2);

  /** build a propositional symbol p */
  Formula formula(const Predicate& p);

  /** build atom p(t) */
  Formula formula(const Predicate& p,const Term& t);

  /** build atom p(t1,t2) */
  Formula formula(const Predicate& p,const Term& t1,const Term& t2);

  /** build atom p(t1,t2,t2) */
  Formula formula(const Predicate& p,const Term& t1,const Term& t2,const Term& t3);

  /** build an annotated formula (i.e. formula that is either axiom, goal, etc...) */
  AnnotatedFormula annotatedFormula(Formula f, FormulaBuilder::Annotation a, Lib::vstring name="");

  /**
   * Add an axiom into the problem
   */
  void addFormula(Formula f);

  /**
   * Add an assumption into the problem
   */
  void assertFormula(Formula f){ addFormula(f); }

  /** 
    * Add a conjecture to the problem
    */
  void addConjecture(Formula f);
  
  /**
   * Add formulas parsed from a stream
   *
   * @param s the stream
   * @param includeDirectory where the parser will look for included files
   *
   * WARNING it is assumed that the syntax of the stream matches the logic
   * of the solver
   */
  void addFromStream(istream& s, vstring includeDirectory="./"); 
  
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
  bool preprocessed;
};




}

#endif // __API_Solver__
