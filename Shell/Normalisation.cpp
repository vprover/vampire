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
 * @file Normalisation.cpp
 * Implementing the normalisation inference rule.
 * @since 25/12/2003 Manchester
 */

#include "Lib/Sort.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"

#include "Normalisation.hpp"

using namespace Kernel;
using namespace Shell;

Normalisation::Normalisation ()
  : _counter(*env.signature)
{
} // Normalisation::Normalisation

/**
 * Normalize a problem
 */
void Normalisation::normalise(Problem& prb)
{
  CALL("Normalisation::normalise");

  UnitList* units = prb.units();
  units = normalise(units);
  prb.units() = units;
}

/**
 * Normalise a list of units by normalising every unit in it and
 * reordering the list.
 * @since 09/06/2007 Manchester
 */
UnitList* Normalisation::normalise (UnitList* units)
{
  CALL("Normalisation::normalise (UnitList*");

  if (UnitList::isEmpty(units)) {
    return units;
  }
  _counter.count(units,1);

  unsigned length = UnitList::length(units);

  // more than one literal
  Sort<Unit*,Normalisation> srt(length,*this);
  UnitList::Iterator us(units);
  while (us.hasNext()) {
    Unit* unit = us.next();
    normalise(unit);
    srt.add(unit);
  }
  srt.sort();
  UnitList* result = UnitList::empty();
  for (int k = length-1;k >= 0;k--) {
    result = new UnitList(srt[k],result);
  }
  UnitList::destroy(units);
  return result;
} // Normalisation::normalise (UnitList*)


/**
 * Normalise the unit.
 * @since 17/07/2003 Manchester, changed to use a new Sort class
 * @since 09/06/2007 Manchester, changed to new datastructures
 */
void Normalisation::normalise (Unit* unit)
{
  CALL ("Normalisation::normalize(Unit*)");

  if (! unit->isClause()) {
    return;
  }

  Clause& clause = *static_cast<Clause*>(unit);
  int length = clause.length();

  if (length <= 1) {
    return;
  }

  // more than one literal
  Sort<Literal*,Normalisation> srt(length,*this);
  for (int i = 0;i < length;i++) {
    srt.add(clause[i]);
  }
  srt.sort();
  for (int i=0;i < length;i++) {
    clause[i] = srt[i];
  }

  clause.notifyLiteralReorder();
  return;
} // Normalisation::normalise(Unit*)


/**
 * Comparison operator, required for using class Sort.
 *
 * @param u1 first unit
 * @param u2 second unit
 * @return true if u1 is less than u2
 * @since 17/07/2003 Manchester
 * @since 03/06/2007 Manchester, changed to new data structures */
bool Normalisation::lessThan (Unit* u1, Unit* u2)
{
  CALL("Normalisation::lessThan (const Unit*...)");

  // the below code should be uncommented, it gives the best behavior
  // on the average
  switch (compare(static_cast<int>(u1->inputType()),static_cast<int>(u2->inputType()))) {
  case LESS:
    return false;
  case EQUAL:
    break;
  case GREATER:
    return true;
  }

  if (u1->isClause()) {
    if (u2->isClause()) {
      return lessThan(static_cast<Clause*>(u1),
		      static_cast<Clause*>(u2));
    }
    return true;
  }
  // u1 is a formula unit

  if (u2->isClause()) {
    return false;
  }
  return lessThan(static_cast<FormulaUnit*>(u1)->formula(),
		  static_cast<FormulaUnit*>(u2)->formula());

} // Normalisation::lessThan(const Unit*...)

/**
 * Compare two clauses assuming they have been normalized
 * beforehand.
 */
bool Normalisation::lessThan(Clause* cl1, Clause* cl2)
{
  if(cl1->length()!=cl2->length()) {
    return cl1->length() < cl2->length();
  }
  unsigned clen=cl1->length();
  for(unsigned i=0;i<clen;i++) {
    Comparison cmp=compare( (*cl1)[i], (*cl2)[i] );
    if(cmp!=EQUAL) {
      return cmp==LESS;
    }
  }
  return false;
}


/**
 * Comparison operator, required for using class Sort.
 *
 * @param f1 first formula
 * @param f2 second formula
 * @return true if f1 is less than f2
 * @since 26/06/2002 Manchester
 * @since 17/07/2003 Manchester, slightly changed
 */
bool Normalisation::lessThan (Formula* f1, Formula* f2)
{
  CALL("Normalisation::lessThan (const Formula*...)");

  return compare(f1,f2) == LESS;
} // Normalisation::lessThan


/**
 * Comparison operator, required for using Sort<...>.
 *
 * @param l1 first literal
 * @param l2 second literal
 * @return true if l1 is less than l2
 * @since 26/06/2002 Manchester
 * @since 17/07/2003 Manchester, slightly changed
 */
bool Normalisation::lessThan (Literal* l1, Literal* l2)
{
  CALL("Normalisation::lessThan (const Literal*...)");

  return compare(l1,l2) == LESS;
}


/**
 * Comparison of normalized formulas.
 *
 * @since 27/06/2002 Manchester
 * @since 17/07/2003 Manchester, changed to non-pointer types
 * @since 11/12/2004 Manchester, true and false added
 */
Comparison Normalisation::compare (Formula* fm1, Formula* fm2)
{
  CALL("Normalisation::compare (const Formula*...)");

  SubformulaIterator sf1(fm1);
  SubformulaIterator sf2(fm2);

  while (sf1.hasNext()) {
    if (! sf2.hasNext()) {
      return GREATER;
    }
    Formula* f1 = sf1.next();
    Formula* f2 = sf2.next();

    Comparison comp = compare ((int)f1->connective(),
			       (int)f2->connective ());
    if (comp != EQUAL) {
      return comp;
    }

    // same connective
    switch (f1->connective()) {
    case LITERAL:
      comp = compare(f1->literal(),f2->literal());
      if (comp != EQUAL) {
        return comp;
      }
      break;

    case BOOL_TERM: {
      TermList ts1 = f1->getBooleanTerm();
      TermList ts2 = f2->getBooleanTerm();
      comp = compare(ts1, ts2);
      if (comp != EQUAL) {
        return comp;
      }
    }
    break;

    case FORALL:
    case EXISTS:
      // first compare the length of the variable prefix,
      //  and then the immediate subformulas
      comp = compare((int) VList::length(f1->vars()),
                     (int) VList::length(f2->vars()));
      if (comp != EQUAL) {
        return comp;
      }
      break;

    default:
      break;
    }
  }
  return sf2.hasNext() ? LESS : EQUAL;
} // Normalisation::compare (const Formula*



/**
 * Comparison of two literals, needed for normalization. All negative
 * literals are smaller than positive ones. Otherwise literals are
 * compared by comparing their atoms.
 *
 * @since 26/06/2002 Manchester
 * @since 17/07/2003 Manchester, slightly changed
 * @since 03/06/2007 Manchester, changed to new data structures
 */
Comparison Normalisation::compare (Literal* l1, Literal* l2)
{
  CALL("Normalisation::compare (const Literal*...)");

  if (l1 == l2) {
    return EQUAL;
  }

  if (!l1->shared() && l2->shared()) {
    return GREATER;
  }

  if (l1->shared() && !l2->shared()) {
    return LESS;
  }

  Comparison comp;

  if (l1->shared() && l2->shared()) {
    comp = compare((int)l1->weight(),(int)l2->weight());
    if (comp != EQUAL) {
  //    return Comparison(-comp);
      return comp;
    }
  }

  // negative literals are less than positive
  if (l1->isPositive()) {
    if (! l2->isPositive()) {
      return GREATER;
    }
  }
  else { // l1 is negative
    if (l2->isPositive()) {
      return LESS;
    }
  }

  // same polarity, compare atoms
  // equality is less than nonequality
  if (l1->isEquality()) {
    if (! l2->isEquality()) {
      return LESS;
    }
  }
  else if (l2->isEquality()) {
    return GREATER;
  }

  int p1 = l1->functor();
  int p2 = l2->functor();
  if (p1 != p2) {
    comp = compare((int)l1->arity(),(int)l2->arity());
    if (comp != EQUAL) {
      return comp;
    }
    if (l1->shared() && l2->shared()) {
      comp = compare((int)l1->vars(),(int)l2->vars());
      if (comp != EQUAL) {
        return comp;
      }
    }
    comp = compare(_counter.getPred(p1).pocc(),
		   _counter.getPred(p2).pocc());
    if (comp != EQUAL) {
      return comp;
    }
    comp = compare(_counter.getPred(p1).nocc(),
		   _counter.getPred(p2).nocc());
    if (comp != EQUAL) {
      return comp;
    }
    comp = compare(_counter.getPred(p1).docc(),
		   _counter.getPred(p2).docc());
    if (comp != EQUAL) {
      return comp;
    }
  }

  for(unsigned i = 0; i < l1->arity(); i++){
    TermList* ts1 = l1->nthArgument(i);
    TermList* ts2 = l2->nthArgument(i);
    comp = compare(*ts1,*ts2);
    if (comp != EQUAL) {
      return comp;
    }
  }
  return EQUAL;
} // Normalisation::compare(const Literal*...)


/**
 * Compare term lists lexicographically, using the comparison
 * order for terms. Terms t1 and t2 are compared using
 * the order described below. t1 is less than t2 if
 * <ol>
 *   <li> t1 is variable and t2 is not, or else</li>
 *   <li> t1 is a numeric term and t2 is not, or else</li>
 *   <li> both are numeric and the value of t1 is less
 *        than the value of t2</li>
 *   <li> both t1,t2 are compound terms and
 *    <ol>
 *      <li> t1.functor &lt; t2.functor, or else</li>
 *      <li> t1.functor = t2.functor and
 *           t1.args &lt; t2.args, using the lexicographic comparison</li>
 *    </ol>
 * </ol>
 * @since 03/06/2007 Manchester, changed to new data structures
 */
Comparison Normalisation::compare(TermList ts1, TermList ts2)
{
  CALL("Normalisation::compare(TermList...)");

  // both non-empty
  if (ts1.isVar() && !ts2.isVar()) {
     return LESS;
  }

  if (!ts1.isVar() && ts2.isVar()) {
    return GREATER;
  }

  if(ts1.isVar() && ts2.isVar()){
    return EQUAL;
  }
  // both non-variables

  Term* t1 = ts1.term();
  Term* t2 = ts2.term();
  return compare(t1,t2);
} // Normalisation::compare (const TermList*...)


/**
 * Compare two non-variable terms.
 * @since 09/06/2007
 */
Comparison Normalisation::compare(Term* t1, Term* t2)
{
  CALL("Normalisation::compare(const Term*...)");


  if (t1 == t2) {
    return EQUAL;
  }

  Comparison comp;

  if (!t1->isSpecial() && t2->isSpecial()) {
    return GREATER;
  }

  if (t1->isSpecial() && !t2->isSpecial()) {
    return LESS;
  }

  if(!t1->isSort() && t2->isSort()){
    return GREATER;
  } 

  if(t1->isSort() && !t2->isSort()){
    return LESS;
  }

  if (t1->isSpecial() && t2->isSpecial()) {
    comp = compare ((int)t1->getSpecialData()->getType(),
                    (int)t2->getSpecialData()->getType());
    if (comp != EQUAL) {
      return comp;
    }

    // same kind of special terms
    switch (t1->getSpecialData()->getType()) {
      case Term::SF_FORMULA:
        return compare(t1->getSpecialData()->getFormula(), t2->getSpecialData()->getFormula());

      case Term::SF_ITE:
        comp = compare(t1->getSpecialData()->getCondition(), t2->getSpecialData()->getCondition());
        if (comp != EQUAL) {
          return comp;
        }
        break; // compare arguments "then" and "else" as usual below

      case Term::SF_LET: {
        comp = compare((int) VList::length(t1->getSpecialData()->getVariables()),
                       (int) VList::length(t2->getSpecialData()->getVariables()));
        if (comp != EQUAL) {
          return comp;
        }
        TermList b1 = t1->getSpecialData()->getBinding();
        TermList b2 = t2->getSpecialData()->getBinding();
        comp = compare(b1, b2);
        if (comp != EQUAL) {
          return comp;
        }
        break; // compare body of the let as usual below (although 1) what about sorts, 2) what about doing the modulo the bound name?)
      }

      case Term::SF_LET_TUPLE: {
        comp = compare((int) VList::length(t1->getSpecialData()->getTupleSymbols()),
                       (int) VList::length(t2->getSpecialData()->getTupleSymbols()));
        if (comp != EQUAL) {
          return comp;
        }
        TermList b1 = t1->getSpecialData()->getBinding();
        TermList b2 = t2->getSpecialData()->getBinding();
        comp = compare(b1, b2);
        if (comp != EQUAL) {
          return comp;
        }
        break; // compare body of the tuple below
      }

      case Term::SF_TUPLE: {
        comp = compare(t1->getSpecialData()->getTupleTerm(), t2->getSpecialData()->getTupleTerm());
        if (comp != EQUAL) {
          return comp;
        }
        break; // compare body of the tuple below
      }

      case Term::SF_LAMBDA: {
        comp = compare((int) VList::length(t1->getSpecialData()->getLambdaVars()),
                       (int) VList::length(t2->getSpecialData()->getLambdaVars()));
        if (comp != EQUAL) {
          return comp;
        }
        TermList b1 = t1->getSpecialData()->getLambdaExp();
        TermList b2 = t2->getSpecialData()->getLambdaExp();
        comp = compare(b1, b2);
        return comp;     
      }

      case Term::SF_MATCH: {
        break; // comparison by arity and pairwise by arguments is done below
      }

      default:
        ASSERTION_VIOLATION;
    }
  }

  if (!t1->shared() && t2->shared()) {
    return GREATER;
  }

  if (t1->shared() && !t2->shared()) {
    return LESS;
  }

  if (t1->shared() && t2->shared()) {
    comp = compare((int)t1->weight(),(int)t2->weight());
    if (comp != EQUAL) {
      return comp;
    }

    comp = compare((int)t1->vars(),(int)t2->vars());
    if (comp != EQUAL) {
      return comp;
    }
  }

  int f1 = t1->functor();
  int f2 = t2->functor();
  if (f1 != f2) {
    comp = compare((int)t1->arity(),(int)t2->arity());
    if (comp != EQUAL) {
      return comp;
    }
    int countf1 = t1->isSort() ? _counter.getTypeCon(f1).occ() : _counter.getFun(f1).occ();
    int countf2 = t1->isSort() ? _counter.getTypeCon(f2).occ() : _counter.getFun(f2).occ();
    comp = compare(countf1, countf2);
    if (comp != EQUAL) {
      return comp;
    }
  }

  for(unsigned i = 0; i < t1->arity(); i++){
    TermList* ts1 = t1->nthArgument(i);
    TermList* ts2 = t2->nthArgument(i);
    comp = compare(*ts1,*ts2);
    if (comp != EQUAL) {
      return comp;
    }
  }
  return EQUAL;
} // Normalisation::compare(const Term*...)
