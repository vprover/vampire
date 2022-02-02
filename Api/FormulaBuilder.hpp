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

//#include "Helper.hpp"

#include "Lib/VString.hpp"

namespace Api {

using namespace std;

/**
 * Exception that is thrown when some of the Api code
 * is used in an invalid manner.
 */
class ApiException
{
public:
  ApiException(Lib::vstring msg)
  : _msg(msg) {}

  /** Description of the cause of the exception */
  Lib::vstring msg() const { return _msg; }
protected:
  Lib::vstring _msg;
};

/**
 * Exception that is thrown when the @b FormulaBuilder related code
 * is used in an invalid manner.
 */
class FormulaBuilderException
: public ApiException
{
public:
  FormulaBuilderException(Lib::vstring msg)
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
  SortMismatchException(Lib::vstring msg)
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
  InvalidTPTPNameException(Lib::vstring msg, Lib::vstring name)
  : FormulaBuilderException(msg), _name(name) {}

  /** The invalid name that caused the exception to be thrown */
  Lib::vstring name() const { return _name; }
private:
  Lib::vstring _name;
};

typedef unsigned Var;
class Sort;
class Function;
class Predicate;
class Term;
class Formula;
class AnnotatedFormula;

/**
 * A factory class for terms, formulas and annotated formulas
 */
class FormulaBuilder
{
public:
  /**
   * Create the API for building formulas
   * @param checkNames - flag to check names of function and predicate symbols. If true,
   *        then an attempt to create a function or a predicate starting with a capital-case
   *        letter will result in an exception
   * @param checkBindingBoundVariables if true, then an attempt to bind an already bound variable
   *        will result in an exception
   * @param allowImplicitlyTypedVariables allow creating variables without explicitely
   *        specifying a type. If false, the Var var(const Lib::vstring& varName) function
   *        will throw and exception.
   * @param outputDummyNames if true, dummy names are output instead of actual predicate names
   */
  FormulaBuilder(bool checkNames=true, bool checkBindingBoundVariables=true,
      bool allowImplicitlyTypedVariables=true, bool outputDummyNames=false);

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

  enum InterpretedPredicate {
    INT_GREATER,
    INT_GREATER_EQUAL,
    INT_LESS,
    INT_LESS_EQUAL,
  };

  /** Annotation of formulas */
  enum Annotation {
    /** Axiom or derives from axioms */
    AXIOM,
    /** Assumption or derives from axioms and assumptions */
    ASSUMPTION,
    /** Goal or derives from the goal */
    CONJECTURE
  };

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

  /**
   * Return the default sort that is used when no sort is specified.
   */
  static Sort defaultSort();

  /** Create a variable with the default sort
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   */
  Var var(const Lib::vstring& varName);

  /** Create a variable
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   * @param varSort sort of the new variable
   */
  Var var(const Lib::vstring& varName, Sort varSort);

  /**
   * Create a function symbol using default sorts. If @b builtIn is true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Functions of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class.
   */
  Function function(const Lib::vstring& funName, unsigned arity, bool builtIn=false);

  /**
   * Create a function symbol with specified range and domain sorts. If @b builtIn is
   * true, the symbol will not be eliminated during preprocessing.
   *
   * @warning Functions of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Function function(const Lib::vstring& funName, unsigned arity, Sort rangeSort, Sort* domainSorts, bool builtIn=false);

  /** Return constant representing @c i */
  Function integerConstant(int i);
  /**
   * Return constant representing @c i
   *
   * @c FormulaBuilderException may be thrown if @c i is not a proper value, or too large
   * for Vampire internal representation.
   */
  Function integerConstant(Lib::vstring i);

  /**
   * Create a predicate symbol using default sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Predicates of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Predicate predicate(const Lib::vstring& predName, unsigned arity, bool builtIn=false);

  /**
   * Create a predicate symbol with specified domain sorts. If @b builtIn if true, the symbol will not be
   * eliminated during preprocessing.
   *
   * @warning Predicates of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Predicate predicate(const Lib::vstring& predName, unsigned arity, Sort* domainSorts, bool builtIn=false);

  /**
   * Create interpreted predicate
   */
  Predicate interpretedPredicate(InterpretedPredicate symbol);

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




  void addAttribute(Predicate p, Lib::vstring name, Lib::vstring value);
  unsigned attributeCount(Predicate p);
  Lib::vstring getAttributeName(Predicate p, unsigned index);
  Lib::vstring getAttributeValue(Predicate p, unsigned index);
  Lib::vstring getAttributeValue(Predicate p, Lib::vstring attributeName);

  void addAttribute(Function fn, Lib::vstring name, Lib::vstring value);
  unsigned attributeCount(Function fn);
  Lib::vstring getAttributeName(Function fn, unsigned index);
  Lib::vstring getAttributeValue(Function fn, unsigned index);
  Lib::vstring getAttributeValue(Function fn, Lib::vstring attributeName);

  void addAttribute(Sort s, Lib::vstring name, Lib::vstring value);
  unsigned attributeCount(Sort s);
  Lib::vstring getAttributeName(Sort s, unsigned index);
  Lib::vstring getAttributeValue(Sort s, unsigned index);
  Lib::vstring getAttributeValue(Sort s, Lib::vstring attributeName);

  /** build a variable term */
  Term varTerm(const Var& v);

  /** build a term f(t,ts) */
  Term term(const Function& f,const Term* args);

  /** build an atomic formula different from equality */
  Formula atom(const Predicate& p, const Term* args, bool positive=true);

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

  /** build a propositional symbol p */
  Formula formula(const Predicate& p);

  /** build atom p(t) */
  Formula formula(const Predicate& p,const Term& t);

  /** build atom p(t1,t2) */
  Formula formula(const Predicate& p,const Term& t1,const Term& t2);

  /** build atom p(t1,t2,t2) */
  Formula formula(const Predicate& p,const Term& t1,const Term& t2,const Term& t3);

  /** build an annotated formula (i.e. formula that is either axiom, goal, etc...) */
  AnnotatedFormula annotatedFormula(Formula f, Annotation a, Lib::vstring name="");


  /**
   * Return copy of term @b original with all occurrences of variable @c v
   * replaced by @c t.
   */
  Term substitute(Term original, Var v, Term t);
  /**
   * Return copy of formula @c f in which every occurrence of @c v
   * was replaced by @c t. @c v must not be bound inside the formula.
   * @c t must no contain any varialbes that are bound inside the formula.
   *
   * @warning Substitution can change order of arguments of the equality
   * predicate.
   */
  Formula substitute(Formula f, Var v, Term t);
  AnnotatedFormula substitute(AnnotatedFormula af, Var v, Term t);

  /**
   * Return copy of term @c original that has all occurrences of term
   * @c replaced replaced by @c target. @c replaced must be a constant.
   */
  Term replaceConstant(Term original, Term replaced, Term target);

  /**
   * Return copy of formula @c f that has all occurrences of term
   * @c replaced replaced by @c target. @c replaced must be a constant.
   * Variables in @c target must not be bound in @c f.
   *
   * @warning Constant replacement can change order of arguments of the equality
   * predicate.
   */
  Formula replaceConstant(Formula f, Term replaced, Term target);
  AnnotatedFormula replaceConstant(AnnotatedFormula f, Term replaced, Term target);
private:
  // FBHelper _aux;

  friend class StringIterator;
  friend class Formula;
  friend class AnnotatedFormula;
};

}

std::ostream& operator<< (std::ostream& str,const Api::Sort& sort);
std::ostream& operator<< (std::ostream& str,const Api::Formula& f);
std::ostream& operator<< (std::ostream& str,const Api::AnnotatedFormula& f);

namespace Api
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

/**
 * An iterator object for strings
 */
class StringIterator
{
public:
  StringIterator() : _impl(0) {};
  explicit StringIterator(const VirtualIterator<Lib::vstring>& vit);
  ~StringIterator();
  StringIterator(const StringIterator& it);
  StringIterator& operator=(const StringIterator& it);

  /**
   * Return true if there is a Lib::vstring to be returned by a call
   * to the @b next() function
   */
  bool hasNext();
  /**
   * Return the next available Lib::vstring
   *
   * The @b hasNext() function must return true before a call
   * to this function.
   */
  Lib::vstring next();

private:
  VirtualIterator<Lib::vstring>* _impl;
};

class Sort
{
public:
  Sort() {}
  explicit Sort(unsigned num) : _num(num) {}
  operator unsigned() const { return _num; }

  static Sort getInvalid() { return Sort(UINT_MAX); }
  bool isValid() const { return _num!=UINT_MAX; }
private:
  unsigned _num;
};

class Function
{
public:
  Function() {}
  explicit Function(unsigned num) : _num(num) {}
  operator unsigned() const { return _num; }
private:
  unsigned _num;
};

class Predicate
{
public:
  Predicate() {}
  explicit Predicate(unsigned num) : _num(num) {}
  operator unsigned() const { return _num; }
private:
  unsigned _num;
};

class Term
{
public:
  Term() : content(0) {}

  Lib::vstring toString() const;

  /**
   * Return true if this object is not initialized to a term
   */
  bool isNull() const { return content==0; }

  /**
   * Return true if term is a variable
   */
  bool isVar() const;

  /**
   * For a variable term return its variable
   */
  Var var() const;

  /**
   * Return the top function of a non-variable term
   */
  Function functor() const;

  /**
   * For a non-variable term, return arity of the top function.
   */
  unsigned arity() const;

  /**
   * Return @c i -th argument of a non-variable term.
   */
  Term arg(unsigned i);

  /**
   * Return sort of the term
   *
   * @warning this function can be used only for terms build by the
   * FormulaBuilder, not for terms coming from the parser.
   */
  Sort sort() const;

  operator Kernel::TermList() const;
  explicit Term(Kernel::TermList t);
  // explicit Term(Kernel::TermList t, ApiHelper aux);

  bool operator==(const Term& o) const {
    return toString()==o.toString();
  }
private:
  size_t content;
  // ApiHelper _aux;

  friend class FormulaBuilder;
  friend class FBHelperCore;
};

class Formula
{
public:
  Formula() : form(0) {}

  Lib::vstring toString() const;

  /**
   * Return true if this object is not initialized to a formula
   */
  bool isNull() const { return form==0; }

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
   * Return the top-level connective of the formula
   */
  FormulaBuilder::Connective connective() const;

  /**
   * If formula is ATOM, return the predicate symbol. If the atom is
   * equality, 0 is returned.
   */
  Predicate predicate() const;

  /**
   * If formula is ATOM, return true if it's polarity is positive and false
   * if it is negative.
   */
  bool atomPolarity() const;

  /**
   * Return number of arguments of the top-level element in formula.
   *
   * If formula is an atom, arity of the predicate symbol is returned.
   */
  unsigned argCnt() const;

  /**
   * Return @c i -th formula argument.
   *
   * For atom formulas, @c termArg() function should be used.
   */
  Formula formulaArg(unsigned i);

  /**
   * Return @c i -th argument of atomic formula.
   */
  Term termArg(unsigned i);

  /**
   * Return iterator on names of free variables
   *
   * Each free variable is returned by the iterator just once
   */
  StringIterator freeVars();

  /**
   * Return iterator on names of bound variables
   *
   * If a variable is bound multiple times, it is returned
   * by the iterator the same number of times as well.
   */
  StringIterator boundVars();

  operator Kernel::Formula*() const { return form; }
  explicit Formula(Kernel::Formula* f) : form(f) {}
  // explicit Formula(Kernel::Formula* f, ApiHelper aux) : form(f), _aux(aux) {}

  bool operator==(const Formula& o) const {
    return toString()==o.toString();
  }
private:
  Kernel::Formula* form;
  // ApiHelper _aux;

  friend class FormulaBuilder;
  friend class FBHelperCore;
  friend class Problem;
};

class AnnotatedFormula
{
public:
  AnnotatedFormula() : unit(0) {}

  Lib::vstring toString() const;

  /**
   * Return name of the annotated formula
   *
   * If a name was specified at the call of the
   * @b FormulaBuilder::annotatedFormula() function, that name is
   * returned, otherwise an automatically generated one is returned.
   */
  Lib::vstring name() const;

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
  StringIterator freeVars();

  /**
   * Return iterator on names of bound variables
   *
   * If a variable is bound multiple times, it is returned
   * by the iterator the same number of times as well.
   */
  StringIterator boundVars();

  /** Return annotation of the annotated formula */
  FormulaBuilder::Annotation annotation() const;

  /** Return the formula inside this annotated formula */
  Formula formula();

  operator Kernel::Unit*() const { return unit; }
  explicit AnnotatedFormula(Kernel::Unit* fu) : unit(fu) {}
  // explicit AnnotatedFormula(Kernel::Unit* fu, ApiHelper aux) : unit(fu), _aux(aux) {}

  bool operator==(const AnnotatedFormula& o) const {
    return toString()==o.toString();
  }
private:
  static void assignName(AnnotatedFormula& form, Lib::vstring name);

  Kernel::Unit* unit;
  // ApiHelper _aux;

  friend class FormulaBuilder;
  friend class Problem;
};

}

#endif // __API_FormulaBuilder__
