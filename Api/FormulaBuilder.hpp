/**
 * @file FormulaBuilder.hpp
 * Defines class FormulaBuilder.
 */

#ifndef __FormulaBuilder__
#define __FormulaBuilder__

#include <string>
#include <ostream>

namespace Api {

using namespace std;

/** Structure with auxiliary data that do not need to appear in the header file */
class DefaultHelperCore;
class FBHelperCore;
class FormulaBuilder;
class StringIterator;

/**
 * A reference counting smart pointer to FBAux
 */
class ApiHelper
{
public:
  ApiHelper();
  ~ApiHelper();
  ApiHelper(const ApiHelper& h);
  ApiHelper& operator=(const ApiHelper& h);
  ApiHelper& operator=(FBHelperCore* hc);
  bool operator==(const ApiHelper& h) const;
  bool operator!=(const ApiHelper& h) const;

  DefaultHelperCore* operator->();
protected:
  void updRef(bool inc);

  FBHelperCore* _obj;
};

class FBHelper
: public ApiHelper
{
public:
  FBHelper();
  FBHelperCore* operator->();
};

/**
 * Exception that is thrown when the @b FormulaBuilder related code

 * is used in an invalid manner.
 */
class FormulaBuilderException
{
public:
  FormulaBuilderException(string msg)
  : _msg(msg) {}

  /** Description of the cause of the exception */
  string msg() const { return _msg; }
protected:
  string _msg;
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
   */
  FormulaBuilder(bool checkNames=true, bool checkBindingBoundVariables=true);

  enum Connective {
    AND,
    OR,
    IMP,
    IFF,
    XOR,
    NOT,
    FORALL,
    EXISTS
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


  /** Create a variable
   * @param varName name of the variable. Must be a valid TPTP variable name, that is, start
   *        with a capital-case letter. If the variable name does not conform to TPTP, an exception
   *        will be raised.
   */
  Var var(const string& varName);

  /** create a function symbol */
  Function function(const string& funName,unsigned arity);

  /** create a predicate symbol */
  Predicate predicate(const string& predName,unsigned arity);

  /** build a variable term */
  Term varTerm(const Var& v);

  /** build a term f(t,ts) */
  Term term(const Function& f,const Term* args);

  /** build an atomic formula different from equality */
  Formula atom(const Predicate& p, const Term* args, bool positive=true);

  /** build an equality */
  Formula equality(const Term& lhs,const Term& rhs, bool positive=true);

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
  AnnotatedFormula annotatedFormula(Formula f, Annotation a, string name="");

private:
  FBHelper _aux;

  friend class StringIterator;
  friend class Formula;
  friend class AnnotatedFormula;
};

}

std::ostream& operator<< (std::ostream& str,const Api::Formula& f);
std::ostream& operator<< (std::ostream& str,const Api::AnnotatedFormula& f);

//Now comes the implementation specific code

namespace Lib
{
template<typename T> class VirtualIterator;
}

namespace Kernel
{
class Formula;
class FormulaUnit;
class TermList;
class Unit;
}

namespace Api
{

using namespace std;
using namespace Lib;

class Problem;

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

  /**
   * Return true if this object is not initialized to a term
   */
  bool isNull() const { return content==0; }

  operator Kernel::TermList() const;
  explicit Term(Kernel::TermList t);
private:
  size_t content;

  friend class FormulaBuilder;
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

  /**
   * Return true if this object is not initialized to
   * an annotated formula
   */
  string toString() const;

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

  operator Kernel::Unit*() const { return unit; }
  explicit AnnotatedFormula(Kernel::Unit* fu) : unit(fu) {}
private:
  Kernel::Unit* unit;
  ApiHelper _aux;

  friend class FormulaBuilder;
  friend class Problem;
};

}

#endif // __FormulaBuilder__
