/**
 * @file FormulaBuilder.hpp
 * Defines class FormulaBuilder.
 */

#ifndef __FormulaBuilder__
#define __FormulaBuilder__

#include <string>
#include <ostream>

#include "Helper.hpp"

namespace Api {

using namespace std;


/**
 * Exception that is thrown when some of the Api code
 * is used in an invalid manner.
 */
class ApiException
{
public:
  ApiException(string msg)
  : _msg(msg) {}

  /** Description of the cause of the exception */
  string msg() const { return _msg; }
protected:
  string _msg;
};

/**
 * Exception that is thrown when the @b FormulaBuilder related code
 * is used in an invalid manner.
 */
class FormulaBuilderException
: public ApiException
{
public:
  FormulaBuilderException(string msg)
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
  SortMismatchException(string msg)
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
  InvalidTPTPNameException(string msg, string name)
  : FormulaBuilderException(msg), _name(name) {}

  /** The invalid name that caused the exception to be thrown */
  string name() const { return _name; }
private:
  string _name;
};

typedef unsigned Sort;
typedef unsigned Var;
typedef unsigned Function;
typedef unsigned Predicate;
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
   *        specifying a type. If false, the Var var(const string& varName) function
   *        will throw and exception.
   */
  FormulaBuilder(bool checkNames=true, bool checkBindingBoundVariables=true, bool allowImplicitlyTypedVariables=true);

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

  /** Annotation of formulas */
  enum Annotation {
    /** Axiom or derives from axioms */
    AXIOM,
    /** Assumption or derives from axioms and assumptions */
    ASSUMPTION,
    /** Lemma or derives from lemmas */
    LEMMA,
    /** Goal or derives from the goal */
    CONJECTURE
  };

  /**
   * Create a sort with name @c sortName. Sort name must be unique, otherwise
   * and exception will be raised.
   */
  Sort sort(const string& sortName);

  /**
   * Return the default sort that is used when no sort is specified.
   */
  static Sort defaultSort();

  /**
   * Return name of the sort @c s.
   */
  string getSortName(Sort s);

  /** Create a variable with the default sort
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   */
  Var var(const string& varName);

  /** Create a variable
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   * @param varSort sort of the new variable
   */
  Var var(const string& varName, Sort varSort);

  /** create a function symbol using default sorts
   *
   * @warning Functions of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Function function(const string& funName, unsigned arity);

  /** create a function symbol with specified range and domain sorts
   *
   * @warning Functions of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Function function(const string& funName, unsigned arity, Sort rangeSort, Sort* domainSorts);

  /** create a predicate symbol using default sorts
   *
   * @warning Predicates of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Predicate predicate(const string& predName, unsigned arity);

  /** create a predicate symbol with specified domain sorts
   *
   * @warning Predicates of the same name and arity must have always
   * also the same type, even across different instances of the
   * FormulaBuilder class. */
  Predicate predicate(const string& predName, unsigned arity, Sort* domainSorts);

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

  /** build an if-then-else formula */
  Formula formula(Connective c,const Formula& cond,const Formula& thenBranch,const Formula& elseBranch);

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
  AnnotatedFormula annotatedFormula(Formula f, Annotation a, string name="");


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
  FBHelper _aux;

  friend class StringIterator;
  friend class Formula;
  friend class AnnotatedFormula;
};

}

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
   * If true, equality is output as $equality_sorted(sort_name, t1,t2) instead of t1=t2.
   * The default value is false.
   */
  static bool sortedEquality() { return _sortedEquality; }
  static void setSortedEquality(bool newVal) { _sortedEquality = newVal; }
private:
  static bool _sortedEquality;
};

/**
 * An iterator object for strings
 */
class StringIterator
{
public:
  StringIterator() : _impl(0) {};
  explicit StringIterator(const VirtualIterator<string>& vit);
  ~StringIterator();
  StringIterator(const StringIterator& it);
  StringIterator& operator=(const StringIterator& it);

  /**
   * Return true if there is a string to be returned by a call
   * to the @b next() function
   */
  bool hasNext();
  /**
   * Return the next available string
   *
   * The @b hasNext() function must return true before a call
   * to this function.
   */
  string next();

private:
  VirtualIterator<string>* _impl;
};

class Term
{
public:
  Term() : content(0) {}

  string toString() const;

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
  explicit Term(Kernel::TermList t, ApiHelper aux);

  bool operator==(const Term& o) const {
    return toString()==o.toString();
  }
private:
  size_t content;
  ApiHelper _aux;

  friend class FormulaBuilder;
  friend class FBHelperCore;
};

class Formula
{
public:
  Formula() : form(0) {}

  string toString() const;

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
  explicit Formula(Kernel::Formula* f, ApiHelper aux) : form(f), _aux(aux) {}

  bool operator==(const Formula& o) const {
    return toString()==o.toString();
  }
private:
  Kernel::Formula* form;
  ApiHelper _aux;

  friend class FormulaBuilder;
  friend class FBHelperCore;
};

class AnnotatedFormula
{
public:
  AnnotatedFormula() : unit(0) {}

  string toString() const;

  /**
   * Return name of the annotated formula
   *
   * If a name was specified at the call of the
   * @b FormulaBuilder::annotatedFormula() function, that name is
   * returned, otherwise an automatically generated one is returned.
   */
  string name() const;

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
  explicit AnnotatedFormula(Kernel::Unit* fu, ApiHelper aux) : unit(fu), _aux(aux) {}

  bool operator==(const AnnotatedFormula& o) const {
    return toString()==o.toString();
  }
private:
  Kernel::Unit* unit;
  ApiHelper _aux;

  friend class FormulaBuilder;
  friend class Problem;
};

}

#endif // __FormulaBuilder__
