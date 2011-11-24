/**
 * @file Formula.hpp
 * Defines class Formula.
 *
 * @since 02/12/2003, Manchester, allocation changed to use Allocator
 * @since 06/05/2007, Manchester, change to use new kind of Term and Literal
 */

#ifndef __Formula__
#define __Formula__

#include <utility>

#include "Forwards.hpp"

#include "Lib/List.hpp"
#include "Lib/XML.hpp"

#include "Connective.hpp"
#include "Term.hpp"

using namespace Lib;

namespace Kernel {

class Literal;
class Formula;

typedef List<Formula*> FormulaList;

class Formula
{
public:
  typedef List<int> VarList;
  /**
   * Constructor of constant formulas (true/false)
   * @since 02/07/2007 Manchester
   */
  explicit Formula (bool value)
    : _connective(value ? TRUE : FALSE)
  {
  } // Formula::Formula (bool value)

  // structure
  /** Return the connective */
  Connective connective () const { return _connective; }

  TermList termLetLhs() const;
  TermList termLetRhs() const;
  Literal* formulaLetLhs() const;
  Formula* formulaLetRhs() const;
  Formula* letBody() const;
  Formula* condArg() const;
  Formula* thenArg() const;
  Formula* elseArg() const;
  const FormulaList* args() const;
  FormulaList* args();
  FormulaList** argsPtr();
  const Formula* left() const;
  Formula* left();
  const Formula* right() const;
  Formula* right();
  const Formula* qarg() const;
  Formula* qarg();
  const VarList* vars() const;
  VarList* vars();
  const Formula* uarg() const;
  Formula* uarg();
  const Literal* literal() const;
  Literal* literal();
  VarList* freeVariables () const;
  VarList* boundVariables () const;

  // miscellaneous
  bool equals(const Formula*) const;
  void collectPredicates(Stack<unsigned>& acc);
  void collectPredicatesWithPolarity(Stack<pair<unsigned,int> >& acc, int polarity=1);

  XMLElement toXML() const;

  // output
  string toString() const;
  string toStringInScopeOf(Connective con) const;
  static string toString(Connective con);
  bool parenthesesRequired(Connective outer) const;
  // auxiliary functions
  void destroy();

  unsigned weight() const;

  Color getColor();
  bool getSkip();

  static Formula* fromClause(Clause* cl, BDDNode* prop);

  static Formula* fromClause(Clause* cl);

  static Formula* quantify(Formula* f);

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("Formula");
  USE_ALLOCATOR(Formula);
protected:
  /** Create a dummy formula will null content */
  explicit Formula(Connective con)
    : _connective(con)
  {}

  /** connective */
  Connective _connective;
  // auxiliary functions
  static string _connectiveNames[];
}; // class Formula

/**
 * Atomic formulas.
 * @since 02/06/2007 Manchester
 */
class AtomicFormula
  : public Formula
{
public:
  /** building atomic formula from a literal */
  explicit AtomicFormula (Literal* lit)
    : Formula(LITERAL),
      _literal(lit)
  {}
  /** Return the literal of this formula */
  const Literal* getLiteral() const { return _literal; }
  /** Return the literal of this formula */
  Literal* getLiteral() { return _literal; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("AtomicFormula");
  USE_ALLOCATOR(AtomicFormula);
protected:
  /** The literal of this formula */
  Literal* _literal;
}; // class AtomicFormula


/**
 * Quantified formulas.
 * @since 02/06/2007 Manchester
 */
class QuantifiedFormula
  : public Formula
{
 public:
  /** Build a quantified formula */
  QuantifiedFormula(Connective con, VarList* vs, Formula* arg)
    : Formula(con),
      _vars(vs),
      _arg(arg)
  {
    ASS(con == FORALL || con == EXISTS);
  }

  /** Return the immediate subformula */
  const Formula* subformula () const { return _arg; }
  /** Return the immediate subformula */
  Formula* subformula () { return _arg; }
  /** Return the list of variables */
  const VarList* varList() const { return _vars; }
  /** Return the list of variables */
  VarList* varList() { return _vars; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("QuantifiedFormula");
  USE_ALLOCATOR(QuantifiedFormula);
 protected:
  /** list of variables */
  VarList* _vars;
  /** argument */
  Formula* _arg;
}; // class Formula::QuantifiedData

/**
 * Negated formula.
 * @since 02/06/2007 Manchester
 */
class NegatedFormula
  : public Formula
{
public:
  /** building a negated formula */
  explicit NegatedFormula (Formula* f)
    : Formula(NOT),
      _arg(f)
  {}

  /** Return the immediate subformula of this formula */
  const Formula* subformula() const { return _arg; }
  /** Return the immediate subformula of this formula */
  Formula* subformula() { return _arg; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("NegatedFormula");
  USE_ALLOCATOR(NegatedFormula);
protected:
  /** The immediate subformula */
  Formula* _arg;
}; // class NegatedFormula


/**
 * Binary formula.
 * @since 02/06/2007 Manchester
 */
class BinaryFormula
  : public Formula
{
public:
  /** building binary formula */
  explicit BinaryFormula (Connective con,Formula* lhs,Formula* rhs)
    : Formula(con),
      _left(lhs),
      _right(rhs)
  {
    ASS(con == IFF || con == XOR || con == IMP);
  }

  /** Return the lhs subformula of this formula */
  const Formula* lhs() const { return _left; }
  /** Return the lhs subformula of this formula */
  Formula* lhs() { return _left; }
  /** Return the rhs subformula of this formula */
  const Formula* rhs() const { return _right; }
  /** Return the rhs subformula of this formula */
  Formula* rhs() { return _right; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("BinaryFormula");
  USE_ALLOCATOR(BinaryFormula);
protected:
  /** The lhs subformula */
  Formula* _left;
  /** The rhs subformula */
  Formula* _right;
}; // class BinaryFormula


/**
 * Conjunction and disjunction.
 * @since 02/06/2007 Manchester
 */
class JunctionFormula
  : public Formula
{
 public:
  JunctionFormula (Connective con, FormulaList* args)
    : Formula(con),
      _args(args)
  {
    ASS(con == AND || con == OR);
    ASS_GE(args->length(),2);
  }

  /** set arguments to args */
  void setArgs(FormulaList* args) { _args = args; }

  /** Return the list of immediate subformulas */
  const FormulaList* getArgs() const { return _args; }
  /** Return the list of immediate subformulas */
  FormulaList* getArgs() { return _args; }
  /** Return a pointer to the list of immediate subformulas */
  FormulaList** getArgsPtr() { return &_args; }

  static Formula* generalJunction(Connective c, FormulaList* args);

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("JunctionFormula");
  USE_ALLOCATOR(JunctionFormula);
 protected:
  /** list of immediate subformulas */
  FormulaList* _args;
}; // class JunctionFormula

/**
 * If-then-else formula.
 */
class IteFormula
  : public Formula
{
 public:
  IteFormula(Formula* condarg, Formula* thenarg, Formula* elsearg)
    : Formula(ITE),
      _condarg(condarg),
      _thenarg(thenarg),
      _elsearg(elsearg)
  {
  }

  /** Return the subformula serving as the condition */
  Formula* condArg() const { return _condarg; }
  /** Return the subformula serving as the then branch */
  Formula* thenArg() const { return _thenarg; }
  /** Return the subformula serving as the else branch */
  Formula* elseArg() const { return _elsearg; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("IteFormula");
  USE_ALLOCATOR(IteFormula);
 protected:
  Formula* _condarg;
  Formula* _thenarg;
  Formula* _elsearg;
}; // class IteFormula

/**
 * Formula let...in formula.
 */
class FormulaLetFormula
  : public Formula
{
 public:
  /**
   * Create a formula (let lhs := rhs in body)
   */
  FormulaLetFormula (Literal* lhs, Formula* rhs, Formula* body)
    : Formula(FORMULA_LET),
      _lhs(lhs),
      _rhs(rhs),
      _body(body)
  {
    ASS(lhs->hasOnlyDistinctVariableArgs());
    ASS(lhs->shared());
  }

  /** Return the literal that should be replaced */
  Literal* lhs() const { return _lhs; }
  /** Return the formula that should replace the @b lhs() literal */
  Formula* rhs() const { return _rhs; }
  /** Return body on which the replacement is performed */
  Formula* body() const { return _body; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("FormulaLetFormula");
  USE_ALLOCATOR(FormulaLetFormula);
 protected:
  Literal* _lhs;
  Formula* _rhs;
  Formula* _body;
}; // class FormulaLetFormula

/**
 * Term let...in formula.
 */
class TermLetFormula
  : public Formula
{
 public:
  /**
   * Create a formula (let lhs := rhs in body)
   */
  TermLetFormula (TermList lhs, TermList rhs, Formula* body)
    : Formula(TERM_LET),
      _lhs(lhs),
      _rhs(rhs),
      _body(body)
  {
    ASS(lhs.isSafe());
    ASS(lhs.isVar() || lhs.term()->hasOnlyDistinctVariableArgs());
  }

  /** Return the term that should be replaced */
  TermList lhs() const { return _lhs; }
  /** Return the term that should replace the @b lhs() term */
  TermList rhs() const { return _rhs; }
  /** Return body on which the replacement is performed */
  Formula* body() const { return _body; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("TermLetFormula");
  USE_ALLOCATOR(TermLetFormula);
 protected:
  TermList _lhs;
  TermList _rhs;
  Formula* _body;
}; // class TermLetFormula

// definitions, had to be put out of class

/** Return the list of variables of a quantified formula */
inline
const Formula::VarList* Formula::vars() const
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<const QuantifiedFormula*>(this)->varList();
}
/** Return the list of variables of a quantified formula */
inline
Formula::VarList* Formula::vars()
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<QuantifiedFormula*>(this)->varList();
}

/** Return the immediate subformula of a quantified formula */
inline
const Formula* Formula::qarg() const
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<const QuantifiedFormula*>(this)->subformula();
}
/** Return the immediate subformula of a quantified formula */
inline
Formula* Formula::qarg()
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<QuantifiedFormula*>(this)->subformula();
}

/** Return the immediate subformula of a negated formula */
inline
const Formula* Formula::uarg() const
{
  ASS(_connective == NOT);
  return static_cast<const NegatedFormula*>(this)->subformula();
}

/** Return the immediate subformula of a negated formula */
inline
Formula* Formula::uarg()
{
  ASS(_connective == NOT);
  return static_cast<NegatedFormula*>(this)->subformula();
}

/** Return the list of immediate subformulas of a junction formula */
inline
const FormulaList* Formula::args() const
{
  ASS(_connective == AND || _connective == OR);
  return static_cast<const JunctionFormula*>(this)->getArgs();
}

/** Return the list of immediate subformulas of a junction formula */
inline
FormulaList* Formula::args()
{
  ASS(_connective == AND || _connective == OR);
  return static_cast<JunctionFormula*>(this)->getArgs();
}

/** Return a pointer to the list of immediate subformulas of a junction formula */
inline
FormulaList** Formula::argsPtr()
{
  ASS(_connective == AND || _connective == OR);
  return static_cast<JunctionFormula*>(this)->getArgsPtr();
}

/** Return the literal of an atomic formula */
inline
const Literal* Formula::literal() const
{
  ASS(_connective == LITERAL);
  return static_cast<const AtomicFormula*>(this)->getLiteral();
}

/** Return the literal of an atomic formula */
inline
Literal* Formula::literal()
{
  ASS(_connective == LITERAL);
  return static_cast<AtomicFormula*>(this)->getLiteral();
}

/** Return the lhs subformula of a binary formula */
inline
const Formula* Formula::left() const
{
  ASS(_connective == IFF || _connective == XOR || _connective == IMP);
  return static_cast<const BinaryFormula*>(this)->lhs();
}
/** Return the lhs subformula of a binary formula */
inline
Formula* Formula::left()
{
  ASS(_connective == IFF || _connective == XOR || _connective == IMP);
  return static_cast<BinaryFormula*>(this)->lhs();
}

/** Return the rhs subformula of a binary formula */
inline
const Formula* Formula::right() const
{
  ASS(_connective == IFF || _connective == XOR || _connective == IMP);
  return static_cast<const BinaryFormula*>(this)->rhs();
}
/** Return the rhs subformula of a binary formula */
inline
Formula* Formula::right()
{
  ASS(_connective == IFF || _connective == XOR || _connective == IMP);
  return static_cast<BinaryFormula*>(this)->rhs();
}
/** Return the condition subformula of an if-then-else formula */
inline
Formula* Formula::condArg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->condArg();
}
/** Return the then-branch subformula of an if-then-else formula */
inline
Formula* Formula::thenArg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->thenArg();
}
/** Return the else-branch subformula of an if-then-else formula */
inline
Formula* Formula::elseArg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->elseArg();
}
inline
Formula* Formula::letBody() const {
  if(_connective == TERM_LET) {
    return static_cast<const TermLetFormula*>(this)->body();
  }
  else {
    ASS(_connective == FORMULA_LET)
    return static_cast<const FormulaLetFormula*>(this)->body();
  }
}
inline
Literal* Formula::formulaLetLhs() const {
  ASS(_connective == FORMULA_LET)
  return static_cast<const FormulaLetFormula*>(this)->lhs();
}
inline
Formula* Formula::formulaLetRhs() const {
  ASS(_connective == FORMULA_LET)
  return static_cast<const FormulaLetFormula*>(this)->rhs();
}
inline
TermList Formula::termLetLhs() const {
  ASS(_connective == TERM_LET);
  return static_cast<const TermLetFormula*>(this)->lhs();
}
inline
TermList Formula::termLetRhs() const {
  ASS(_connective == TERM_LET);
  return static_cast<const TermLetFormula*>(this)->rhs();
}

// operators

std::ostream& operator<< (ostream& out, const Formula& f);

}

#endif // __Formula__
