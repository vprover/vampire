/**
 *  @file Formula.cpp
 *  Implements class Formula.
 */

#include <string>

#include "../Debug/Tracer.hpp"

#include "../Lib/Exception.hpp"
#include "../Lib/MultiCounter.hpp"

#include "Term.hpp"
#include "Formula.hpp"
#include "SubformulaIterator.hpp"
#include "FormulaVarIterator.hpp"

using namespace Lib;

namespace Kernel {

// /**
//  * Turn literal list into a formula representing the disjunction of
//  * these literals.
//  *
//  * @since 10/10/2004 Manchester
//  */
// void Formula::makeFromLiteralList (const LiteralList& from,Formula& to)
// {
//   CALL("Formula::makeFromLiteralList");

//   if (from.isEmpty()) {
//     to = Formula(FALSE);
//     return;
//   }
//   if (from.tail().isEmpty()) {
//     to = Formula(from.head());
//     return;
//   }
//   // at least two literals
//   FormulaList fs;
//   FormulaList::makeFromLiteralList(from,fs);
//   to = Formula(OR,fs);
// } // Formula::makeFromLiteralList

// /**
//  * Construct a list of formulas from a non-empty list of literals
//  * @since 10/10/2004 Manchester
//  */
// void FormulaList::makeFromLiteralList (const LiteralList& ls,FormulaList& fs)
// {
//   CALL("FormulaList::makeFromLiteralList");

//   Lib::ListPusher<Formula> stack(fs);
//   Lib::Iterator<Literal> lits(ls);
//   while (lits.hasNext()) {
//     Formula f(lits.next());
//     stack.push(f);
//   }
// } // FormulaList::FormulaList


/**
 * Destroy the content of the formula. The destruction depends on the type
 * of this formula.
 *
 * @since 11/12/2004 Manchester, true and false added
 * @since 02/06/2007 Manchester, rewritten for new data types
 */
void Formula::destroy ()
{
  CALL ("Formula::Data::destroy");
  ASS (this);

  switch ( connective() ) {
  case LITERAL:
    delete static_cast<AtomicFormula*>(this);
    return;

  case AND:
  case OR:
    delete static_cast<JunctionFormula*>(this);
    return;

  case IMP:
  case IFF:
  case XOR:
    delete static_cast<BinaryFormula*>(this);
    return;

  case NOT:
    delete static_cast<NegatedFormula*>(this);
    return;

  case FORALL:
  case EXISTS:
    delete static_cast<QuantifiedFormula*>(this);
    return;

  case TRUE:
  case FALSE:
    delete this;
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
    return;
#endif
  }
} // Formula::Data::deref ()


// // the total number of symbols in the formula
// // a bug fixed 30/06/2001, flight Kopenhagen-Manchester
// int Formula::weight () const
// {
//   switch ( connective () ) {
//     case LITERAL:
//       return atom()->weight();

//     case AND:
//     case OR: {
//       int sz = -1;

//       for ( List* fs = args(); fs->isNonEmpty (); fs = fs->tail() )
//         sz += fs->head()->weight() + 1;

//       return sz;
//     }

//     case IMP:
//     case IFF:
//     case XOR:
//       return left()->weight() +
//              right()->weight () + 1;

//     case NOT:
//       return arg()->weight () + 1;

//     case FORALL:
//     case EXISTS:
//       return vars()->length() + arg()->weight () + 1;

//     default:
//       ASSERTION_VIOLATION;
//       return 0;
//   }
// } // Formula::weight

// /**
//  * Convert the formula to an XML element.
//  * @since 29/11/2003 Manchester
//  * @since 11/12/2004 Manchester, true and false added
//  */
// XMLElement Formula::toXML() const
// {
//   XMLElement f("formula");
//   f.addAttribute("connective",_connectiveNames[connective()]);

//   switch ( connective() ) {
//   case LITERAL:
//     f.addChild(literal()->toXML());
//     return f;

//   case AND:
//   case OR:
//     {
//       FormulaList::Iterator fs(args());
//       while (fs.hasNext()) {
// 	f.addChild(fs.next()->toXML());
//       }
//     }
//     return f;

//   case IMP:
//   case IFF:
//   case XOR:
//     f.addChild(left()->toXML());
//     f.addChild(right()->toXML());
//     return f;

//   case NOT:
//     f.addChild(uarg()->toXML());
//     return f;

//   case FORALL:
//   case EXISTS:
//     {
//       XMLElement vs("variables");
//       VarList::Iterator variables(vars());
//       while (variables.hasNext()) {
// 	vs.addChild(Term::variableToXML(variables.next()));
//       }
//       f.addChild(vs);
//       f.addChild(qarg()->toXML());
//     }
//     return f;

//   case TRUE:
//   case FALSE:
//     return f;

// #if VDEBUG
//   default:
//     ASSERTION_VIOLATION;
// #endif
//   }
// } // Formula::toXML()

/**
 * Convert the connective to a string.
 * @since 02/01/2004 Manchester
 */
string Formula::toString (Connective c)
{
  static string names [] =
//    { "", "&", "\\/", "=>", "<=>", "<~>", "~", "!", "?", "false", "true"};
    { "", "&", "|", "=>", "<=>", "<~>", "~", "!", "?", "false", "true"};

  return names[(int)c];
} // Formula::toString (Connective c)



/**
 * Convert the formula to a string using the native syntax
 *
 * @since 12/10/2002 Tbilisi, implemented as ostream output function
 * @since 09/12/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
string Formula::toString () const
{
  CALL("Formula::toString");

  Connective c = connective();
  string con = toString(c);

  switch (c) {
  case LITERAL:
    return literal()->toString();

  case AND:
  case OR:
    {
      ASS (args()->length() >= 2);
      string result = args()->head()->toStringInScopeOf(c);
      FormulaList::Iterator arg(args()->tail());
      while (arg.hasNext()) {
	result += ' ' + con + ' ' + arg.next()->toStringInScopeOf(c);
      }
      return result;
    }

  case IMP:
  case IFF:
  case XOR:
    return left()->toStringInScopeOf(c) + ' ' + con + ' ' +
           right()->toStringInScopeOf(c);

  case NOT:
    {
      const Formula* arg = uarg();
      if (arg->connective() == LITERAL) {
	return con + arg->literal()->toString();
      }
      return con + arg->toStringInScopeOf(c);
    }

  case FORALL:
  case EXISTS:
    {
//      string result = "(" + con;
//      VarList::Iterator vs(vars());
//      while (vs.hasNext()) {
//	result += string(" ") + Term::variableToString(vs.next());
//      }
//      result += ")";
      string result = con + " [";
      VarList::Iterator vs(vars());
      bool first=true;
      while (vs.hasNext()) {
	if(!first) {
	  result+= ",";
	}
	result += Term::variableToString(vs.next());
	first=false;
      }
      result += "] : ";
      return result + qarg()->toStringInScopeOf(c);
    }

  case TRUE:
  case FALSE:
    return con;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Formula::toString


/**
 * True if the formula needs parentheses around itself
 * when in scope of outer.
 *
 * @since 21/09/2002 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
bool Formula::parenthesesRequired (Connective outer) const
{
  CALL("Formula::parenthesesRequired");

  switch (connective())
    {
    case LITERAL:
    case NOT:
    case FORALL:
    case EXISTS:
    case TRUE:
    case FALSE:
      return false;

    case OR:
    case AND:
      return outer != IMP &&
	     outer != IFF &&
             outer != XOR;

    case IMP:
      return outer != IFF &&
	     outer != XOR;

    case IFF:
    case XOR:
      return true;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return false;
#endif
    }
} // Formula::parenthesesRequired


/**
 * Convert the formula in scope of another formula
 * to a string using the native syntax.
 * @param outer connective of the outer formula
 * @since 09/12/2003 Manchester
 */
string Formula::toStringInScopeOf (Connective outer) const
{
  return parenthesesRequired(outer) ?
         string("(") + toString() + ")" :
         toString();
} // Formula::toStringInScopeOf


// /**
//  * True if this formula is equal to f.
//  *
//  * @since 23/12/2003 Manchester
//  * @since 11/12/2004 Manchester, true and false added
//  */
// bool Formula::equals (const Formula& f) const
// {
//   if (*this == f) {
//     return true;
//   }
//   if (connective() != f.connective()) {
//     return false;
//   }

//   switch (connective())
//     {
//     case LITERAL:
//       return literal()->equals(f.literal());

//     case AND:
//     case OR:
//       return args().equals(f.args());

//     case IMP:
//     case IFF:
//     case XOR:
//       return left().equals(f.left()) &&
//              right().equals(f.right());

//     case NOT:
//       return uarg().equals(f.uarg());

//     case FORALL:
//     case EXISTS:
//       {
// 	// first check that the variables are equal
// 	Iterator<int> vs(vars());
// 	Iterator<int> ws(f.vars());
// 	while (vs.hasNext()) {
// 	  if (! ws.hasNext()) {
// 	    return false;
// 	  }
// 	  if (vs.next() != ws.next()) {
// 	    return false;
// 	  }
// 	}
// 	if (ws.hasNext()) {
// 	  return false;
// 	}
//       }
//       // and then compare immediate subformulas
//       return qarg().equals(f.qarg());

//     case TRUE:
//     case FALSE:
//       return true;

// #if VDEBUG
//     default:
//       ASSERTION_VIOLATION;
// #endif
//     }
// }

// /**
//  * True if this list is equal to fs.
//  * @since 23/12/2003 Manchester
//  */
// bool FormulaList::equals (const FormulaList& fs) const
// {
//   if (isEmpty()) {
//     return fs.isEmpty();
//   }
//   return fs.isNonEmpty() &&
//          head().equals(fs.head()) &&
//          tail().equals(fs.tail());
// } // FormulaList::equals

/**
 * Return the list all free variables of the formula.
 * @since 12/12/2004 Manchester
 */
Formula::VarList* Formula::freeVariables () const
{
  FormulaVarIterator fvi(this);
  VarList* result = VarList::empty();
  VarList::FIFO stack(result);
  while (fvi.hasNext()) {
    stack.push(fvi.next());
  }
  return result;
} // Formula::freeVariables

/**
 * Compute the weight of the formula: the number of connectives plus the
 * weight of all atoms.
 * @since 23/03/2008 Torrevieja
 */
unsigned Formula::weight() const
{
  CALL("Formula::weight");

  unsigned result;

  SubformulaIterator fs(const_cast<Formula*>(this));
  while (fs.hasNext()) {
    const Formula* f = fs.next();
    switch (f->connective()) {
    case LITERAL:
      result += f->literal()->weight();
      break;
    default:
      result++;
      break;
    }
  }
  return result;
} // Formula::weight

/**
 * Return color of the formula
 *
 * We do not store the color of the formula, so it gets
 * computed again each time the function is called.
 */
Color Formula::getColor()
{
  CALL("Formula::getColor");

  SubformulaIterator si(this);
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(f->literal()->color()!=COLOR_TRANSPARENT) {
      return f->literal()->color();
    }
  }
  return COLOR_TRANSPARENT;
}

/**
 * Return true iff the formula is VIP for the purpose of
 * symbol elimination
 */
bool Formula::getVIP()
{
  CALL("Formula::getColor");

  SubformulaIterator si(this);
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(f->literal()->vip()) {
      return true;
    }
  }
  return false;
}


/*
  THIS IS USEFUL
  switch (connective()) {
  case LITERAL:
  case AND:
  case OR:
  case IMP:
  case IFF:
  case XOR:
  case NOT:
  case FORALL:
  case EXISTS:
  case TRUE:
  case FALSE:
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
*/

}
