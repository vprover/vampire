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

class FormulaBuilderException
{
public:
  FormulaBuilderException(string msg)
  : _msg(msg) {}
  string msg() const { return _msg; }
protected:
  string _msg;
};

class InvalidTPTPNameException
: public FormulaBuilderException
{
public:
  InvalidTPTPNameException(string msg, string name)
  : FormulaBuilderException(msg), _name(name) {}

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

class FormulaBuilder
{
public:
  /**
   * Create the API for building formulas
   * @param checkNames - flag to check names of function and predicate symbols. If true,
   *        then an attempt to create a function or a predicate starting with a capital-case
   *        letter will result in an exception
   */
  FormulaBuilder(bool checkNames=true);

  ~FormulaBuilder();

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
  AnnotatedFormula annotatedFormula(Formula f, Annotation a);

private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  FormulaBuilder(const FormulaBuilder&);
  FormulaBuilder& operator=(const FormulaBuilder&);

  struct FBAux;

  /** structure with auxiliary data that do not need to appear in the header file */
  FBAux* _aux;
};

}

std::ostream& operator<< (std::ostream& str,const Api::Formula& f);
std::ostream& operator<< (std::ostream& str,const Api::AnnotatedFormula& f);

//Now comes the implementation specific code

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

class Problem;

class Term
{
public:
  operator Kernel::TermList() const;
  Term(Kernel::TermList t);
private:
  size_t content;

  friend class FormulaBuilder;
};

class Formula
{
public:
  Formula() : form(0) {}

  string toString() const;

  operator Kernel::Formula*() const { return form; }
  Formula(Kernel::Formula* f) : form(f) {}
private:
  Kernel::Formula* form;

  friend class FormulaBuilder;
};

class AnnotatedFormula
{
public:
  AnnotatedFormula() {}

  string toString() const;

  operator Kernel::Unit*() const { return unit; }
  AnnotatedFormula(Kernel::Unit* fu) : unit(fu) {}
private:
  Kernel::Unit* unit;

  friend class FormulaBuilder;
  friend class Problem;
};

}

#endif // __FormulaBuilder__
