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
 *  @file Formula.cpp
 *  Implements class Formula.
 */

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/VString.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"

#include "Shell/Options.hpp"

#include "Clause.hpp"
#include "Term.hpp"
#include "Formula.hpp"
#include "SubformulaIterator.hpp"
#include "FormulaVarIterator.hpp"

using namespace Lib;

namespace Kernel {

vstring Formula::DEFAULT_LABEL = "none";


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
  // ASS (this); -- new gcc thinks this is never null

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

  case BOOL_TERM:
    delete static_cast<BoolTermFormula*>(this);

  case TRUE:
  case FALSE:
    delete this;
    return;

  case NAME:
    delete static_cast<NamedFormula*>(this);
    return;

  case NOCONN:
    ASSERTION_VIOLATION;
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

/**
 * Convert the connective to a vstring.
 * @since 02/01/2004 Manchester
 */
vstring Formula::toString (Connective c)
{
  static vstring names [] =
    { "", "&", "|", "=>", "<=>", "<~>", "~", "!", "?", "$var", "$false", "$true","",""};
  ASS_EQ(sizeof(names)/sizeof(vstring), NOCONN+1);

  return names[(int)c];
} // Formula::toString (Connective c)

/**
 *
 */
vstring Formula::toString(const Formula* formula)
{
  CALL("Formula::toString(const Formula*)");

  vstring res;

  // render a connective if specified, and then a Formula (or ")" of formula is nullptr)
  typedef struct {
    bool wrapInParenthesis;
    Connective renderConnective; // NOCONN means ""
    const Formula* theFormula;   // nullptr means render ")" instead
  } Todo;

  Stack<Todo> stack;
  stack.push({false,NOCONN,formula});

  while (stack.isNonEmpty()) {
    Todo todo = stack.pop();

    // in any case start by rendering the connective passed from "above"
    {
      vstring con = toString(todo.renderConnective);
      if (con != "") {
        res += " "+con+" ";
      }
    }

    const Formula* f = todo.theFormula;

    if (!f) {
      res += ")";
      continue;
    }

    if (todo.wrapInParenthesis) {
      res += "(";
      stack.push({false,NOCONN,nullptr}); // render the final closing bracket
    }

    Connective c = f->connective();
    switch (c) {
    case NAME:
      res += static_cast<const NamedFormula*>(f)->name();
      continue;
    case LITERAL:
      res += f->literal()->toString();
      continue;

    case AND:
    case OR:
      {
        // we will reverse the order
        // but that should not matter

        const FormulaList* fs = f->args();
        ASS (FormulaList::length(fs) >= 2);

        while (FormulaList::isNonEmpty(fs)) {
          const Formula* arg = fs->head();
          fs = fs->tail();
          // the last argument, which will be printed first, is the only one not preceded by a rendering of con
          stack.push({arg->parenthesesRequired(c),FormulaList::isNonEmpty(fs) ? c : NOCONN,arg});
        }

        continue;
      }

    case IMP:
    case IFF:
    case XOR:
      // here we can afford to keep the order right

      stack.push({f->right()->parenthesesRequired(c),c,f->right()});      // second argument with con
      stack.push({f->left()->parenthesesRequired(c),NOCONN,f->left()}); // first argument without con

      continue;

    case NOT:
      {
        res += toString(c);

        const Formula* arg = f->uarg();
        stack.push({arg->parenthesesRequired(c),NOCONN,arg});

        continue;
      }
    case FORALL:
    case EXISTS:
      {
        res += toString(c) + " [";
        VList::Iterator vs(f->vars());
        SList::Iterator ss(f->sorts());
        bool hasSorts = f->sorts();
        bool first=true;
        while (vs.hasNext()) {
          int var = vs.next();
          if (!first) {
            res += ",";
          }
          res += Term::variableToString(var);
          TermList t;
          if (hasSorts) {
            ASS(ss.hasNext());
            t = ss.next();
            if (t != AtomicSort::defaultSort()) {
              res += " : " + t.toString();
            }
          } else if (SortHelper::tryGetVariableSort(var, const_cast<Formula*>(f),t) && t != AtomicSort::defaultSort()) {
            res += " : " + t.toString();
          }
          first = false;
        }
        res += "] : ";

        const Formula* arg = f->qarg();
        stack.push({arg->parenthesesRequired(c),NOCONN,arg});

        continue;
      }

    case BOOL_TERM: {
      vstring term = f->getBooleanTerm().toString();
      res += env.options->showFOOL() ? "$formula{" + term + "}" : term;

      continue;
    }

    case TRUE:
    case FALSE:
      res += toString(c);
      continue;

    case NOCONN:
      ASSERTION_VIOLATION;
  }
  }

  return res;
}

/**
 * Convert the formula to a vstring using the native syntax
 *
 * @since 12/10/2002 Tbilisi, implemented as ostream output function
 * @since 09/12/2003 Manchester
 * @since 11/12/2004 Manchester, true and false added
 */
vstring Formula::toString () const
{
  CALL("Formula::toString");

  return toString(this);
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
    case BOOL_TERM:
    case TRUE:
    case FALSE:
    case NAME:
      return false;

    case OR:
    case AND:
    case IMP:
    case IFF:
    case XOR:
      return true;

    case NOCONN:
      ASSERTION_VIOLATION;
    }

  ASSERTION_VIOLATION;
} // Formula::parenthesesRequired


/**
 * Convert the formula in scope of another formula
 * to a vstring using the native syntax.
 * @param outer connective of the outer formula
 * @since 09/12/2003 Manchester
 */
vstring Formula::toStringInScopeOf (Connective outer) const
{
  return parenthesesRequired(outer) ?
         vstring("(") + toString() + ")" :
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
 * Return the list of all free variables of the formula
 *
 * Each variable in the formula is returned just once.
 *
 * NOTE: don't use this function, if you don't actually need a List
 * (FormulaVarIterator is a better choice)
 *
 * NOTE: remember to free the list when done with it
 * (otherwise we leak memory!)
 *
 * @since 12/12/2004 Manchester
 */
VList* Formula::freeVariables () const
{
  CALL("Formula::freeVariables");

  FormulaVarIterator fvi(this);
  VList* result = VList::empty();
  VList::FIFO stack(result);
  while (fvi.hasNext()) {
    stack.push(fvi.next());
  }
  return result;
} // Formula::freeVariables

bool Formula::isFreeVariable(unsigned var) const
{
  CALL("Formula::isFreeVariable");

  FormulaVarIterator fvi(this);
  while (fvi.hasNext()) {
    if (var == fvi.next()) {
      return true;
    }
  }
  return false;
}

/**
 * Return the list of all bound variables of the formula
 *
 * If a variable is bound multiple times in the formula,
 * it appears in the list the same number of times as well.
 */
VList* Formula::boundVariables () const
{
  CALL("Formula::boundVariables");

  VList* res = VList::empty();
  SubformulaIterator sfit(const_cast<Formula*>(this));
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective() == FORALL || sf->connective() == EXISTS) {
      VList* qvars = sf->vars();
      VList* qvCopy = VList::copy(qvars);
      res = VList::concat(qvCopy, res);
    }
  }
  return res;
}

/**
 * Add into @c acc numbers of all atoms in the formula.
 *
 * As we are collecting atoms, for negative literals we insert their
 * complements.
 */
void Formula::collectAtoms(Stack<Literal*>& acc)
{
  CALL("Formula::collectPredicates");

  SubformulaIterator sfit(this);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()==LITERAL) {
      Literal* l = sf->literal();
      acc.push(Literal::positiveLiteral(l));
    }
  }
}

/**
 * Add into @c acc numbers of all predicates in the formula.
 */
void Formula::collectPredicates(Stack<unsigned>& acc)
{
  CALL("Formula::collectPredicates");

  SubformulaIterator sfit(this);
  while(sfit.hasNext()) {
    Formula* sf = sfit.next();
    if(sf->connective()==LITERAL) {
      acc.push(sf->literal()->functor());
    }
  }
}

void Formula::collectPredicatesWithPolarity(Stack<pair<unsigned,int> >& acc, int polarity)
{
  CALL("Formula::collectPredicatesWithPolarity");

  switch (connective()) {
    case LITERAL:
    {
      Literal* l=literal();
      int pred = l->functor();
      acc.push(make_pair(pred, l->isPositive() ? polarity : -polarity));
      return;
    }

    case AND:
    case OR: {
      FormulaList::Iterator fs(args());
      while (fs.hasNext()) {
	fs.next()->collectPredicatesWithPolarity(acc,polarity);
      }
      return;
    }

    case IMP:
      left()->collectPredicatesWithPolarity(acc,-polarity);
      right()->collectPredicatesWithPolarity(acc,polarity);
      return;

    case NOT:
      uarg()->collectPredicatesWithPolarity(acc,-polarity);
      return;

    case IFF:
    case XOR:
      left()->collectPredicatesWithPolarity(acc,0);
      right()->collectPredicatesWithPolarity(acc,0);
      return;

    case FORALL:
    case EXISTS:
      qarg()->collectPredicatesWithPolarity(acc,polarity);
      return;

    case BOOL_TERM:
      ASSERTION_VIOLATION;

    case TRUE:
    case FALSE:
      return;

    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
  }
}


/**
 * Compute the weight of the formula: the number of connectives plus the
 * weight of all atoms.
 * @since 23/03/2008 Torrevieja
 */
unsigned Formula::weight() const
{
  CALL("Formula::weight");

  unsigned result=0;

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

Formula* JunctionFormula::generalJunction(Connective c, FormulaList* args)
{
  if(!args) {
    if(c==AND) {
      return new Formula(true);
    }
    else {
      ASS_EQ(c,OR);
      return new Formula(false);
    }
  }
  if(!args->tail()) {
    return FormulaList::pop(args);
  }
  return new JunctionFormula(c, args);
}

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
 * Return true iff the formula is Skip for the purpose of
 * symbol elimination
 */
bool Formula::getSkip()
{
  CALL("Formula::getColor");

  SubformulaIterator si(this);
  while(si.hasNext()) {
    Formula* f=si.next();
    if(f->connective()!=LITERAL) {
      continue;
    }

    if(!f->literal()->skip()) {
      return false;
    }
  }
  return true;
}

Formula* Formula::trueFormula()
{
  CALL("Formula::trueFormula");

  static Formula* res = new Formula(true);
  return res;
}

Formula* Formula::falseFormula()
{
  CALL("Formula::falseFormula");

  static Formula* res = new Formula(false);
  return res;
}

/**
 * Creates a formula of the form $ite(c, a, b), where a, b, c are formulas
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createITE(Formula* condition, Formula* thenArg, Formula* elseArg)
{
  CALL("Formula::createITE");
  TermList thenTerm(Term::createFormula(thenArg));
  TermList elseTerm(Term::createFormula(elseArg));
  TermList iteTerm(Term::createITE(condition, thenTerm, elseTerm, AtomicSort::boolSort()));
  return new BoolTermFormula(iteTerm);
}

/**
 * Creates a formula of the form $let(lhs := rhs, body), where body is a formula
 * and lhs and rhs form a binding for a function
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createLet(unsigned functor, VList* variables, TermList body, Formula* contents)
{
  CALL("Formula::createLet(TermList)");
  TermList contentsTerm(Term::createFormula(contents));
  TermList letTerm(Term::createLet(functor, variables, body, contentsTerm, AtomicSort::boolSort()));
  return new BoolTermFormula(letTerm);
}

/**
 * Creates a formula of the form $let(lhs := rhs, body), where body is a formula
 * and lhs and rhs form a binding for a predicate
 * @since 16/04/2015 Gothenburg
 */
Formula* Formula::createLet(unsigned predicate, VList* variables, Formula* body, Formula* contents)
{
  CALL("Formula::createLet(Formula*)");
  TermList bodyTerm(Term::createFormula(body));
  TermList contentsTerm(Term::createFormula(contents));
  TermList letTerm(Term::createLet(predicate, variables, bodyTerm, contentsTerm, AtomicSort::boolSort()));
  return new BoolTermFormula(letTerm);
}

Formula* Formula::quantify(Formula* f)
{
  Set<unsigned> vars;
  FormulaVarIterator fvit( f );
  while(fvit.hasNext()) {
    vars.insert(fvit.next());
  }

  //we have to quantify the formula
  VList* varLst = VList::empty();
  Set<unsigned>::Iterator vit(vars);
  while(vit.hasNext()) {
    VList::push(vit.next(), varLst);
  }
  if(varLst) {
    //TODO could compute the sorts list, but don't want to!
    f=new QuantifiedFormula(FORALL, varLst, 0, f);
  }
  return f;
}


/**
 * Return formula equal to @b cl 
 * that has all variables quantified
 */
Formula* Formula::fromClause(Clause* cl)
{
  CALL("Formula::fromClause");
  
  FormulaList* resLst=0;
  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    Formula* lf=new AtomicFormula((*cl)[i]);
    FormulaList::push(lf, resLst);
  }

  Formula* res=JunctionFormula::generalJunction(OR, resLst);
  
  Set<unsigned> vars;
  FormulaVarIterator fvit( res );
  while(fvit.hasNext()) {
    vars.insert(fvit.next());
  }

  //we have to quantify the formula
  VList* varLst = VList::empty();
  Set<unsigned>::Iterator vit(vars);
  while(vit.hasNext()) {
    VList::push(vit.next(), varLst);
  }
  if(varLst) {
    //TODO could compute the sorts list, but don't want to!
    res=new QuantifiedFormula(FORALL, varLst, 0, res);
  }

  return res;
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

std::ostream& operator<< (ostream& out, const Formula& f)
{
  CALL("operator <<(ostream&, const Formula&)");
  return out << f.toString();
}

std::ostream& operator<< (ostream& out, const Formula* f)
{
  CALL("operator <<(ostream&, const Formula&)");
  return out << f->toString();
}

}
