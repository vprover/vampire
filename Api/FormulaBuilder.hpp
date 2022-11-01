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

#ifndef __API_FormulaBuilder__
#define __API_FormulaBuilder__

#include <ostream>
#include <climits>

#include "Helper.hpp"

#include <vector>
#include <string>

namespace Vampire {

using namespace std;

/**
 * Exception that is thrown when some of the Api code
 * is used in an invalid manner.
 */
class ApiException
{
public:
  ApiException(std::string msg)
  : _msg(msg) {}

  /** Description of the cause of the exception */
  std::string msg() const { return _msg; }
protected:
  std::string _msg;
};

/**
 * Exception that is thrown when the @b FormulaBuilder related code
 * is used in an invalid manner.
 */
class FormulaBuilderException
: public ApiException
{
public:
  FormulaBuilderException(std::string msg)
  : ApiException(msg) {}
};


/**
 * Exception that is thrown when the sort of the argument term and
 * parent symbol are different.
 */
class SortMismatchException
: public FormulaBuilderException
{
public:
  SortMismatchException(std::string msg)
  : FormulaBuilderException(msg) {}
};

/**
 * Exception that is thrown when a name is given that is not
 * a valid TPTP name for respective entity.
 */
class InvalidTPTPNameException
: public FormulaBuilderException
{
public:
  InvalidTPTPNameException(std::string msg, std::string name)
  : FormulaBuilderException(msg), _name(name) {}

  /** The invalid name that caused the exception to be thrown */
  std::string name() const { return _name; }
private:
  std::string _name;
};

typedef unsigned Var;
class Sort;
class Symbol;
class Expression;
class AnnotatedFormula;
class Field;

/* Enum used to provide special semantics to symbols 
 * coming from Rapid program translations
 */
enum RapidSym {
  LEMMA_PRED,
  FN_LOOP_COUNT,
  MAIN_END,
  TIME_POINT,
  CONST_VAR,
  PROGRAM_VAR,
  MALLOC,  
  CHAIN,  
  NULL_PTR,
  OBJ_ARRAY,
  STRUCT_FIELD_SELF_POINTER,
  NONE
};

/**
 * A factory class for terms, formulas and annotated formulas
 */
class FormulaBuilder
{

private:
  /**
   * Create the API for building formulas
   * @param checkNames - flag to check names of function and predicate symbols. If true,
   *        then an attempt to create a function or a predicate starting with a capital-case
   *        letter will result in an exception
   * @param checkBindingBoundVariables if true, then an attempt to bind an already bound variable
   *        will result in an exception
   * @param allowImplicitlyTypedVariables allow creating variables without explicitely
   *        specifying a type. If false, the Var var(const string& varName) function
   *        will throw and exception.
   * @param outputDummyNames if true, dummy names are output instead of actual predicate names
   */
  FormulaBuilder(bool checkNames=true, bool checkBindingBoundVariables=true,
      bool allowImplicitlyTypedVariables=true, bool outputDummyNames=false);

  /** Annotation of formulas */
  enum Annotation {
    /** Axiom or derives from axioms */
    AXIOM,
    /** Assumption or derives from axioms and assumptions */
    ASSUMPTION,
    /** Goal or derives from the goal */
    CONJECTURE
  };

  /** Connective of formulas */
  enum Connective {
    AND,
    OR,
    EXISTS,
    FORALL
  };

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
  /** Sort representing timepoints. Rapid sepcific*/
  Sort timeSort();
  /** Return array sort */
  Sort arraySort(const Sort& indexSort, const Sort& innerSort);
  
  /** Return the sort of formulas */
  static Sort boolSort();

  /**
   * Return the default sort that is used when no sort is specified.
   */
  static Sort defaultSort();

  /** creates a field object that can be used when declaring a struct */
  Field field(std::string& fieldName, Sort fieldSort);

  Field field(std::string& fieldName, Sort fieldSort, std::string& chain,
    std::string& support);

  /** Create a variable with the default sort
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   */
  Var var(const std::string& varName);

  /** Create a variable
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   * @param varSort sort of the new variable
   */
  Var var(const std::string& varName, Sort varSort);

  /**
   * Create a symbol with specified range and domain sorts (BOOL_SORT for predicates). 
   * If @b builtIn is true, the symbol will not be eliminated during preprocessing.
   *
   * @warning Functions of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Symbol symbol(const std::string& funName, unsigned arity, Sort rangeSort, 
    std::vector<Sort>& domainSorts, RapidSym rs = RapidSym::NONE, bool builtIn=false);

  /** Return constant symbol representing @c i */
  Symbol integerConstant(int i);

  /**
   * Return constant symbol representing @c i
   *
   * @c FormulaBuilderException may be thrown if @c i is not a proper value, or too large
   * for Vampire internal representation.
   */
  Symbol integerConstant(std::string i);

  Symbol rationalConstantSymbol(std::string r);

  Symbol realConstantSymbol(std::string r);

  /**
   * Create interpreted predicate
   */
  //Symbol interpretedSymbol(Kernel::Theory::Interpretation interp);

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

  /** build a term f(t,ts) */
  Expression term(const Symbol& f,const std::vector<Expression>& args);

  /** build an equality */
  Expression equality(const Expression& lhs,const Expression& rhs, bool positive=true);

  /** build an equality and check the sorts of the equality sides to be equal to @c sort*/
  Expression equality(const Expression& lhs,const Expression& rhs, Sort sort, bool positive=true);

  /** build a true formula */
  Expression trueFormula();

  /** build a false formula */
  Expression falseFormula();

  /** build the negation of f */
  Expression negation(const Expression& f);

  /** build f1 /\ f2 */
  Expression andFormula(const Expression& f1,const Expression& f2);

  Expression andFormula(const std::vector<Expression>& conjuncts);

  /** build f1 \/ f2 */
  Expression orFormula(const Expression& f1,const Expression& f2);

  Expression orFormula(const std::vector<Expression>& disjuncts);

  Expression andOrOrFormula(Connective con, const std::vector<Expression>& forms);

  /** build f1 -> f2 */
  Expression implies(const Expression& f1,const Expression& f2);

  /** build f1 <-> f2 */
  Expression iff(const Expression& f1,const Expression& f2);

  /** build f1 XOR f2 */
  Expression exor(const Expression& f1,const Expression& f2);

  /** build quantified formula (q v)f */
  Expression forall(const Var& v,const Expression& f);

  /** build quantified formula (q v)f */
  Expression exists(const Var& v,const Expression& f);

  Expression quantifiedFormula(Connective con, const Var& v,const Expression& f);
  // Special cases, convenient to have

  /** build a constant expression c */
  Expression term(const Symbol& c);

  /** build a unary term f(t) */
  Expression term(const Symbol& s,const Expression& t);

  /** build a binary term f(t1,t2) */
  Expression term(const Symbol& s,const Expression& t1,const Expression& t2);

  /** build a term f(t1,t2,t3) */
  Expression term(const Symbol& s,const Expression& t1,const Expression& t2,const Expression& t3);

  /** Build a conditional: if cond then t1 else t2 */
  Expression ite(const Expression& cond,const Expression& t1,const Expression& t2); 

  /** Return constant representing @c i */
  Expression integerConstantTerm(int i);

  /** Return constant representing @c i */
  Expression integerConstantTerm(std::string i);

  /** Return constant representing @c i */
  Expression rationalConstant(std::string r);

  /** Return constant representing @c i */
  Expression realConstant(std::string r);

  /** build t1 + t2 */
  Expression sum(const Expression& t1,const Expression& t2);

  /** build t1 - t2 */
  Expression difference(const Expression& t1,const Expression& t2);

  /** build t1 x t2 */
  Expression multiply(const Expression& t1,const Expression& t2);

  /** build t1 / t2 */
  Expression div(const Expression& t1,const Expression& t2);

  /** build t1 mod t2 */
  Expression mod(const Expression& t1,const Expression& t2);

  /** build -t */
  Expression neg(const Expression& t);

  /** convert t to a real */
  Expression int2real(const Expression& t);

  /** convert t to an integer */
  Expression real2int(const Expression& t);

  /** build floor(t1) */
  Expression floor(const Expression& t1);

  /** create ceiling (t1) */
  Expression ceiling(const Expression& t1);

  /** build  | t1 | */
  Expression absolute(const Expression& t1);
  
  /** build the formula t1 >= t2 */
  Expression geq(const Expression& t1, const Expression& t2);

  /** build the formula t1 <= t2 */
  Expression leq(const Expression& t1, const Expression& t2);

  /** build the formula t1 > t2 */
  Expression gt(const Expression& t1, const Expression& t2);

  /** build the formula t1 < t2 */
  Expression lt(const Expression& t1, const Expression& t2);

  /** build expression store(array, index, newval) */
  Expression store(const Expression& array, const Expression& index, const Expression& newVal);

  /** Build the term select(array, index) */
  Expression select(const Expression& array, const Expression& index);

  /** build an annotated formula (i.e. formula that is either axiom, goal, etc...) */
  AnnotatedFormula annotatedFormula(Expression& f, Annotation a, std::string name="");

  void checkForNumericalSortError(std::initializer_list<Expression> exprs);
  void checkForTermError(std::initializer_list<Expression> exprs);
  template<class T>
  void checkForValidity(std::initializer_list<T> list);

  /**
   * Return copy of expression @b original with all occurrences of variable @c v
   * replaced by @c t.
   * 
   * If @c original is a formula, @c v must not be bound inside the formula.
   * @c t must no contain any varialbes that are bound inside the formula.
   *
   * @warning Substitution can change order of arguments of the equality
   * predicate.
   */
  Expression substitute(Expression original, Var v, Expression t);

  AnnotatedFormula substitute(AnnotatedFormula af, Var v, Expression t);

  /**
   * Return copy of term @c original that has all occurrences of term
   * @c replaced replaced by @c target. @c replaced must be a constant.
   */
  Expression replaceConstant(Expression original, Expression replaced, Expression target);

  /** Return true if function and predicate symbols need to be checked for
    * syntactic correctness.
    */
  bool checkNames();

  void reset();

  /**
   * Return copy of formula @c f that has all occurrences of term
   * @c replaced replaced by @c target. @c replaced must be a constant.
   * Variables in @c target must not be bound in @c f.
   *
   * @warning Constant replacement can change order of arguments of the equality
   * predicate.
   */

  // The old method of carrying this out was to create a formula level let statement
  // and then use FOOLElimination to get rid of the let.
  // Formula level lets are no longer supported, so we need to find another
  // strategy.
  //Formula replaceConstant(Formula f, Term replaced, Term target);
  //AnnotatedFormula replaceConstant(AnnotatedFormula f, Term replaced, Term target);
  FBHelper _aux;

  friend class Solver;
  friend class StringIterator;
  friend class Expression;
  friend class AnnotatedFormula;
};

}

std::ostream& operator<< (std::ostream& str,const Vampire::Sort& sort);
std::ostream& operator<< (std::ostream& str,const Vampire::Expression& f);
std::ostream& operator<< (std::ostream& str,const Vampire::AnnotatedFormula& f);

namespace Vampire
{

using namespace std;
using namespace Lib;

class Problem;

class OutputOptions
{
public:
  /**
   * If true, equality is output as $$equality_sorted(sort_name, t1,t2) instead of t1=t2.
   * The default value is false.
   */
  static bool sortedEquality() { return _sortedEquality; }
  static void setSortedEquality(bool newVal) { _sortedEquality = newVal; }

  /**
   * If true, clauses and formulas are output as tff with all quantified variables.
   * The default value is false.
   */
  static bool tffFormulas() { return _tffFormulas; }
  static void setTffFormulas(bool newVal) { _tffFormulas = newVal; }

  /**
   * If false, names assigned to formulas will be ignored.
   */
  static bool assignFormulaNames() { return _assignFormulaNames; }
  static void setAssignFormulaNames(bool newVal);
private:
  static bool _sortedEquality;
  static bool _tffFormulas;
  static bool _assignFormulaNames;
};

//TODO, update the iterator to return std::strings
/**
 * An iterator object for strings
 */
/*class StringIterator
{
public:
  StringIterator() : _impl(0) {};
  explicit StringIterator(const VirtualIterator<Lib::vstring>& vit);
  ~StringIterator();
  StringIterator(const StringIterator& it);
  StringIterator& operator=(const StringIterator& it);

  
  // Return true if there is a Lib::vstring to be returned by a call
  // to the @b next() function
   
  //bool hasNext();
  
   * Return the next available Lib::vstring
   *
   * The @b hasNext() function must return true before a call
   * to this function.
   
  //Lib::vstring next();

//private:
//  VirtualIterator<Lib::vstring>* _impl;
//}; */


class Sort
{
public:
  Sort() {}
  explicit Sort(Kernel::TermList s);
  explicit Sort(Kernel::TermList s, ApiHelper aux);

  operator Kernel::TermList() const;
  bool operator==(const Sort& o) const;
  bool operator!=(const Sort& o) const;

  bool isTupleSort() const;
  bool isArraySort() const;
  bool isBoolSort() const;

  std::string toString() const;

  bool isVar() const;
  /** the arity of a sort */
  unsigned arity() const;
  /** the index sort of an array sort */
  Sort indexSort() const;
  /** the inner sort of an array sort */
  Sort innerSort() const;

  static Sort getInvalid();
  bool isValid() const;  
private:
  ApiHelper _aux;

  size_t _content;
  friend class FormulaBuilder;
};

class Field
{
public:
  Field(std::string name, Sort sort) : 
   _fieldName(name), _sort(sort), _hasChain(false) {}

  Field(std::string name, Sort sort, std::string chain, std::string support) : 
   _fieldName(name), _sort(sort), _hasChain(true), _chain(chain), _support(support) {}

  std::string name() { return _fieldName; }
  std::string chain() { return _chain; }
  std::string support() { return _support; }
  Sort sort() { return _sort; }
  bool hasChain() { return _hasChain; }

private:
  ApiHelper _aux;
  
  std::string _fieldName;
  Sort _sort;
  bool _hasChain;
  std::string _chain;
  std::string _support;
  friend class FormulaBuilder;  
};


class Symbol
{
public:
  Symbol(){}
  explicit Symbol(unsigned num, bool pred) : _num(num), _pred(pred) {}
  explicit Symbol(unsigned num, bool pred, ApiHelper aux) : 
           _aux(aux), _num(num), _pred(pred) {}
  
  operator unsigned() const { return _num; }

  bool isFunctionSymbol() const { return !_pred; }
private:
  ApiHelper _aux;

  bool isValid() const;

  unsigned _num;
  bool _pred;

  friend class FBHelperCore;
  friend class FormulaBuilder;
};

/** Class to represents terms and formulas.
 *  Most SMT solver APIs do not differentiate between the two.
 *  To allow Vampire to mimic an SMT solver more easily,
 *  we do the same.
 */

class Expression
{
public:
  //cannot create a formula with this constructor
  Expression() : _isTerm(1), _content(0) {}

  std::string toString() const;

  /**
   * Return true if this object is not initialized to a term
   * or formula
   */
  bool isNull() const { return !_content; }


  /**
   * Return true if this expression is not of Boolean sort
   */
  bool isTerm() const { return _isTerm; }

  /**
   * Return true if expression is a variable
   */
  bool isVar() const;

  /**
   * Return true if the expression is a conditional
   */
  bool isIte() const;

  /**
   * For a variable expression return its variable
   */
  Var var() const;

  /**
   * Return the top function / predicate symbol of a non-variable expression
   */
  Symbol functor() const;

  /**
   * Return the sort of this expression
   */
  Sort sort() const;

  /**
   * For a non-variable expression, return arity of the top function
   * or connective (in the case of a formula)
   */
  unsigned arity() const;

  /**
   * Return true if this is a true formula
   */
  bool isTrue() const;

  /**
   * Return true if this is a false formula
   */
  bool isFalse() const;

  /**
   * Return true if the topmost connective is a negation
   */
  bool isNegation() const;

  /**
   * If expression is ATOM, return true if it's polarity is positive and false
   * if it is negative.
   */
  bool atomPolarity() const;

  /**
   * Return @c i -th argument of expression.
   * Throws an error if the index is out of range.
   */
  Expression arg(unsigned i);

  /**
   * Return iterator on names of free variables
   *
   * Each free variable is returned by the iterator just once
   */
  //StringIterator freeVars();

  /**
   * Return iterator on names of bound variables
   *
   * If a variable is bound multiple times, it is returned
   * by the iterator the same number of times as well.
   */
  //StringIterator boundVars();

  operator Kernel::TermList() const;
  operator Kernel::Formula*() const;

  bool operator==(const Expression& e) const {
    return toString()==e.toString();
  }

private:  

  explicit Expression(Kernel::TermList t);
  explicit Expression(Kernel::TermList t, ApiHelper aux);

  explicit Expression(Kernel::Formula* f) : _isTerm(0), _form(f) {}
  explicit Expression(Kernel::Formula* f, ApiHelper aux) : _isTerm(0), _form(f), _aux(aux) {}

  Expression formulaArg(unsigned i);
  bool isValid() const; 

  bool _isTerm;

  union {
    /** reference to a formula */
    Kernel::Formula* _form;
    /** if a term, contains a TermlList */
    size_t _content;
  };

  ApiHelper _aux;

  friend class FormulaBuilder;
  friend class FBHelperCore;
  friend class Problem;
  friend class AnnotatedFormula;  
};


class AnnotatedFormula
{
public:
  AnnotatedFormula() : unit(0) {}

  std::string toString() const;

  /**
   * Return name of the annotated formula
   *
   * If a name was specified at the call of the
   * @b FormulaBuilder::annotatedFormula() function, that name is
   * returned, otherwise an automatically generated one is returned.
   */
  std::string name() const;

  /**
   * Return true if this object is not initialized to
   * an annotated formula
   */
  bool isNull() const { return unit==0; }

  /**
   * Return iterator on names of free variables
   *
   * Each free variable is returned by the iterator just once
   */
 //StringIterator freeVars();

  /**
   * Return iterator on names of bound variables
   *
   * If a variable is bound multiple times, it is returned
   * by the iterator the same number of times as well.
   */
 // StringIterator boundVars();

  /** Return annotation of the annotated formula */
  FormulaBuilder::Annotation annotation() const;

  /** Return the formula inside this annotated formula */
  Expression formula();

  operator Kernel::Unit*() const { return unit; }
  explicit AnnotatedFormula(Kernel::Unit* fu) : unit(fu) {}
  explicit AnnotatedFormula(Kernel::Unit* fu, ApiHelper aux) : unit(fu), _aux(aux) {}

  bool operator==(const AnnotatedFormula& o) const {
    return toString()==o.toString();
  }
private:
  static void assignName(AnnotatedFormula& form, std::string name);

  Kernel::Unit* unit;
  ApiHelper _aux;

  bool isValid() const;

  friend class FormulaBuilder;
  friend class Problem;
};

}

#endif // __API_FormulaBuilder__
