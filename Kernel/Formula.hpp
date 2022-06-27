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

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Connective.hpp"
#include "Term.hpp"


namespace Kernel {

using namespace Lib;

class Formula
{
public:
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

  const FormulaList* args() const;
  FormulaList* args();
  FormulaList** argsPtr();
  const Formula* left() const;
  Formula* left();
  const Formula* right() const;
  Formula* right();
  const Formula* qarg() const;
  Formula* qarg();
  const VList* vars() const;
  VList* vars();
  const SList* sorts() const;
  SList* sorts();
  const Formula* uarg() const;
  Formula* uarg();
  const Literal* literal() const;
  Literal* literal();
  const TermList getBooleanTerm() const;
  TermList getBooleanTerm();
  VList* freeVariables () const;
  bool isFreeVariable(unsigned var) const;
  VList* boundVariables () const;

  // miscellaneous
  bool equals(const Formula*) const;
  void collectAtoms(Stack<Literal*>& acc);
  void collectPredicates(Stack<unsigned>& acc);
  void collectPredicatesWithPolarity(Stack<pair<unsigned,int> >& acc, int polarity=1);

  // output
  vstring toString() const;
  vstring toStringInScopeOf(Connective con) const;
  static vstring toString(Connective con);
  bool parenthesesRequired(Connective outer) const;
  // auxiliary functions
  void destroy();

  unsigned weight() const;

  Color getColor();
  bool getSkip();

  bool hasLabel(){ return _label != DEFAULT_LABEL; }
  vstring getLabel(){ return _label;}
  void label(vstring l){ _label=l; }

  static Formula* fromClause(Clause* cl);

  static Formula* quantify(Formula* f);

  static Formula* trueFormula();
  static Formula* falseFormula();

  static Formula* createITE(Formula* condition, Formula* thenArg, Formula* elseArg);
  static Formula* createLet(unsigned functor, VList* variables, TermList body, Formula* contents);
  static Formula* createLet(unsigned predicate, VList* variables, Formula* body, Formula* contents);


  // use allocator to (de)allocate objects of this class
  CLASS_NAME(Formula);
  USE_ALLOCATOR(Formula);
protected:
  static vstring toString(const Formula* f);

  /** Create a dummy formula will null content */
  explicit Formula(Connective con)
    : _connective(con), _label(DEFAULT_LABEL)
  {}

  /** connective */
  Connective _connective;

  static vstring DEFAULT_LABEL;
  vstring _label;

}; // class Formula

/**
 * Named formulas
 * @since 04/12/2015
 */
class NamedFormula
  : public Formula
{
public:
  explicit NamedFormula(vstring name) : Formula(NAME), _name(name) {}

  CLASS_NAME(NamedFormula);
  USE_ALLOCATOR(NamedFormula);

  vstring name(){ return _name; }
  const vstring name() const { return _name;}

protected:
  vstring _name;

}; // class NamedFormula

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
  CLASS_NAME(AtomicFormula);
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
  QuantifiedFormula(Connective con, VList* vs, SList* ss, Formula* arg)
    : Formula(con),
      _vars(vs),
      _sorts(ss),
      _arg(arg)
  {
    ASS(con == FORALL || con == EXISTS);
    ASS(vs);
    ASS(!ss || VList::length(vs) == SList::length(ss));
  }

  /** Return the immediate subformula */
  const Formula* subformula () const { return _arg; }
  /** Return the immediate subformula */
  Formula* subformula () { return _arg; }
  /** Return the list of variables */
  const VList* varList() const { return _vars; }
  /** Return the list of variables */
  VList* varList() { return _vars; }
  /** Return the list of sorts */
  const SList* sortList() const { return _sorts; }
  /** Return the list of sorts */
  SList* sortList() { return _sorts; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME(QuantifiedFormula);
  USE_ALLOCATOR(QuantifiedFormula);
 protected:
  /** list of variables */
  VList* _vars;
  /** list of sorts */
  SList* _sorts;
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
  CLASS_NAME(NegatedFormula);
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
  CLASS_NAME(BinaryFormula);
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
    ASS_GE(FormulaList::length(args),2);
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
  CLASS_NAME(JunctionFormula);
  USE_ALLOCATOR(JunctionFormula);
 protected:
  /** list of immediate subformulas */
  FormulaList* _args;
}; // class JunctionFormula


/**
 * A formula that is just a boolean term.
 * @since 02/06/2007 Manchester
 */
class BoolTermFormula
  : public Formula
{
 public:
  BoolTermFormula (TermList ts)
    : Formula(BOOL_TERM),
      _ts(ts)
  {
    // only boolean terms in formula context are expected here
    ASS_REP(ts.isVar() || ts.term()->isITE() || ts.term()->isLet() ||
            ts.term()->isTupleLet() || ts.term()->isMatch() ||
            SortHelper::getResultSort(ts.term()) == AtomicSort::boolSort(), ts.toString());
  }

  static Formula* create(TermList ts) {
    if (ts.isVar()) {
      return new BoolTermFormula(ts);
    }

    Term* term = ts.term();
    if (term->isSpecial()) {
      Term::SpecialTermData *sd = term->getSpecialData();
      switch (sd->getType()) {
        case Term::SF_FORMULA:
          return sd->getFormula();
        default:
          return new BoolTermFormula(ts);
      }
    } else {
      unsigned functor = term->functor();
      if (env.signature->isFoolConstantSymbol(true, functor)) {
        return new Formula(true);
      } else {
        ASS(env.signature->isFoolConstantSymbol(false, functor));
        return new Formula(false);
      }
    }
  }

  /** Return the variable */
  const TermList getTerm() const { return _ts; }
  TermList getTerm() { return _ts; }

  // use allocator to (de)allocate objects of this class
  CLASS_NAME(BoolTermFormula);
  USE_ALLOCATOR(BoolTermFormula);
 protected:
  /** boolean term */
  TermList _ts;
}; // class BoolTermFormula

// definitions, had to be put out of class

/** Return the list of variables of a quantified formula */
inline
const VList* Formula::vars() const
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<const QuantifiedFormula*>(this)->varList();
}
/** Return the list of variables of a quantified formula */
inline
VList* Formula::vars()
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<QuantifiedFormula*>(this)->varList();
}

/** Return the list of sorts of a quantified formula */
inline
const SList* Formula::sorts() const
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<const QuantifiedFormula*>(this)->sortList();
}
/** Return the list of sorts of a quantified formula */
inline
SList* Formula::sorts()
{
  ASS(_connective == FORALL || _connective == EXISTS);
  return static_cast<QuantifiedFormula*>(this)->sortList();
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

inline
const TermList Formula::getBooleanTerm() const
{
  ASS(_connective == BOOL_TERM);
  return static_cast<const BoolTermFormula*>(this)->getTerm();
}
inline
TermList Formula::getBooleanTerm()
{
  ASS(_connective == BOOL_TERM);
  return static_cast<BoolTermFormula*>(this)->getTerm();
}

// operators

std::ostream& operator<< (ostream& out, const Formula& f);
std::ostream& operator<< (ostream& out, const Formula* f);

}

#endif // __Formula__
