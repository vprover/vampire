/**
 * @file Formula.hpp
 * Defines class Formula.
 *
 * @since 02/12/2003, Manchester, allocation changed to use Allocator
 * @since 06/05/2007, Manchester, change to use new kind of Term and Literal
 */

#ifndef __Formula__
#define __Formula__

#include "Lib/List.hpp"
#include "Lib/XML.hpp"

#include "Connective.hpp"

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

  Formula* condarg() const;
  Formula* thenarg() const;
  Formula* elsearg() const;
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
  IteFormula (Connective con, Formula* condarg, Formula * thenarg, Formula * elsearg)
    : Formula(con),
      _condarg(condarg),
      _thenarg(thenarg),
      _elsearg(elsearg)
  {
    ASS(con == ITE);
  }

  /** Return the subformula serving as the condition */
  Formula* condarg() const { return const_cast<Formula*>(_condarg); }
  /** Return the subformula serving as the then branch */
  Formula* thenarg() const { return const_cast<Formula*>(_thenarg); }
  /** Return the subformula serving as the else branch */
  Formula* elsearg() const { return const_cast<Formula*>(_elsearg); }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME("IteFormula");
  USE_ALLOCATOR(IteFormula);
 protected:
  Formula* _condarg;
  Formula* _thenarg;
  Formula* _elsearg;
}; // class IteFormula


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
Formula* Formula::condarg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->condarg();
}
/** Return the then-branch subformula of an if-then-else formula */
inline
Formula* Formula::thenarg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->thenarg();
}
/** Return the else-branch subformula of an if-then-else formula */
inline
Formula* Formula::elsearg() const {
  ASS(_connective == ITE);
  return static_cast<const IteFormula*>(this)->elsearg();
}


}

#endif // __Formula__
