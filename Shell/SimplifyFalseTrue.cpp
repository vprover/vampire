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
 * @file SimplifyFalseTrue.cpp
 * Implements class SimplifyFalseTrue implementing simplification
 * of formulas containing true or false.
 *
 * @since 11/12/2004 Manchester
 */

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Environment.hpp"

#include "Shell/Options.hpp"

#include "SimplifyFalseTrue.hpp"

using namespace Kernel;
using namespace Shell;
using namespace Lib;

/**
 * Simplify the unit.
 *
 * @since 11/12/2004 Manchester
 * @since 14/04/2005 Manchester, return value changed to boolean.
 * @return the simplified unit, coincides with the input unit if not changed
 * @warning the unit must contain a formula
 * @since 09/06/2007 Manchester, changed to new datastructures
 */
FormulaUnit* SimplifyFalseTrue::simplify (FormulaUnit* unit)
{
  CALL("SimplifyFalseTrue::simplify(Unit*)");
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = simplify(f);
  if (f == g) { // not simplified
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,FormulaTransformation(InferenceRule::REDUCE_FALSE_TRUE,unit));

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] simplify in: " << unit->toString() << std::endl;
    env.out() << "[PP] simplify out: " << res->toString() << std::endl;
    env.endOutput();
  }
  return res;
} // SimplifyFalseTrue::simplify


/**
 * Simplify subformula.
 *
 * @since 30/08/2002 Torrevieja, return type changed to void
 * @since 23/01/2004 Manchester, changed to include info about positions
 * @since 11/12/2004 Manchester, true and false added
 * @since 09/06/2007 Manchester, changed to new datastructures
 * @since 27/03/2008 Torrevieja, AND/OR case changed considerably
 */
Formula* SimplifyFalseTrue::innerSimplify (Formula* f)
{
  CALL("SimplifyFalseTrue::innerSimplify(Formula*)");

  Connective con = f->connective();
  switch (con) {
  case TRUE:
  case FALSE:
    return f;

  case BOOL_TERM:
    {
      TermList ts = simplify(f->getBooleanTerm());
      if (ts.isTerm()) {
        for (bool constant : { true, false }) {
          if (env.signature->isFoolConstantSymbol(constant, ts.term()->functor())) {
            return new Formula(constant);
          }
        }
      }
      if (ts == f->getBooleanTerm()) {
        return f;
      }
      return new BoolTermFormula(ts);
    }

  case LITERAL:
    {
      Literal* literal = f->literal();

      if (!literal->shared()) {
        bool simplified = false;
        Stack<TermList> arguments;
        Term::Iterator lit(literal);
        while (lit.hasNext()) {
          TermList argument = lit.next();
          TermList simplifiedArgument = simplify(argument);
          if (argument != simplifiedArgument) {
            simplified = true;
          }
          arguments.push(simplifiedArgument);
        }

        if (literal->isEquality() && !literal->isTwoVarEquality()) {
          for (unsigned argument : { 0u, 1u }) {
            if (arguments[argument].isTerm()) {
              bool isTrue  = env.signature->isFoolConstantSymbol(true,  arguments[argument].term()->functor());
              bool isFalse = env.signature->isFoolConstantSymbol(false, arguments[argument].term()->functor());
              if (isTrue || isFalse) {
                Formula* simplifiedFormula = BoolTermFormula::create(arguments[argument == 0 ? 1 : 0]);
                return (isTrue == literal->polarity()) ? simplifiedFormula
                                                       : (Formula*) new NegatedFormula(simplifiedFormula);
              }
            }
          }
        }

        if (!simplified) {
          return f;
        }
        return new AtomicFormula(Literal::create(literal, arguments.begin()));
      }

      return f;
    }

  case AND:
  case OR: 
    {
      int length = 0;  // the length of the result
      bool changed = false;
      FormulaList* fs = f->args();
      DArray<Formula*> gs(FormulaList::length(fs));

      FormulaList::Iterator it(fs);
      while (it.hasNext()) {
	Formula* h = it.next();
	Formula* g = simplify(h);
	switch (g->connective()) {
	case TRUE:
	  if (con == OR) {
	    return g;
	  }
	  if (con == AND) {
	    changed = true;
	    break;
	  }
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;

	case FALSE:
	  if (con == AND) {
	    return g;
	  }
	  if (con == OR) {
	    changed = true;
	    break;
	  }
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;

	default:
	  gs[length++] = g;
	  if (h != g) {
	    changed = true;
	  }
	  break;
	}
      }
      if (! changed) {
	return f;
      }
      switch (length) {
      case 0:
	return new Formula(con == OR ? false : true);
      case 1:
	return gs[0];
      default:
	FormulaList* res = FormulaList::empty();
	for (int l = length-1;l >= 0;l--) {
	  FormulaList::push(gs[l],res);
	}
	return new JunctionFormula(con,res);
      }
    }

  case IMP:
    {
      Formula* right = simplify(f->right());
      if (right->connective() == TRUE) {
	return right;
      }
      Formula* left = simplify(f->left());

      switch (left->connective()) {
      case TRUE: // T -> R
	return right;
      case FALSE: // F -> R
	return new Formula(true);
      default: // L -> R;
	break;
      }

      if (right->connective() == FALSE) {
	return new NegatedFormula(left);
      }
      if (left == f->left() && right == f->right()) {
	return f;
      }
      return new BinaryFormula(con,left,right);
    }

  case IFF:
  case XOR: 
    {
      Formula* left = simplify(f->left());
      Formula* right = simplify(f->right());

      Connective lc = left->connective();
      Connective rc = right->connective();

      switch (lc) {
      case FALSE: // F * _
	switch (rc) {
	case FALSE: // F * F
	  return con == XOR
	         ? right
	         : new Formula(true);
	case TRUE: // F * T
	  return con == XOR
	         ? right
     	         : left;
	default: // F * R
	  return con == XOR
	         ? right
 	         : new NegatedFormula(right);
	}
      case TRUE: // T * _
	switch (rc) {
	case FALSE: // T * F
	  return con == XOR
	         ? left
	         : right;
	case TRUE: // T * T
	  return con == XOR
 	         ? new Formula(false)
     	         : left;
	default: // T * R
	  return con == XOR
 	         ? new NegatedFormula(right)
     	         : right;
	}
      default: // L * _
	switch (rc) {
	case FALSE: // L * F
	  return con == XOR
	         ? left
 	         : new NegatedFormula(left);
	case TRUE:  // L * T
	  return con == XOR
 	         ? new NegatedFormula(left)
     	         : left;
	default:    // L * R
	  if (left == f->left() && right == f->right()) {
	    return f;
	  }
	  return new BinaryFormula(con,left,right);
	}
      }
    }
    
  case NOT: 
    {
      Formula* arg = simplify(f->uarg());
      switch (arg->connective()) {
      case FALSE:
	return new Formula(true);
      case TRUE:
	return new Formula(false);
      default:
	return arg == f->uarg() ? f : new NegatedFormula(arg);
      }
    }
    
  case FORALL:
  case EXISTS: 
    {
      Formula* arg = simplify(f->qarg());
      switch (arg->connective()) {
      case FALSE:
      case TRUE:
	return arg;
      default:
	return arg == f->qarg()
               ? f
               : new QuantifiedFormula(con,f->vars(),f->sorts(),arg);
      }
    }

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
} // SimplifyFalseTrue::simplify ()


TermList SimplifyFalseTrue::simplify(TermList ts)
{
  CALL("SimplifyFalseTrue::simplify(TermList)");

  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();

  if (term->shared()) {
    return ts;
  }

  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        Formula* simplifiedFormula = simplify(sd->getFormula());
        switch (simplifiedFormula->connective()) {
          case TRUE: {
            return TermList(Term::foolTrue());
          }
          case FALSE: {
            return TermList(Term::foolFalse());
          }
          default: {
            if (simplifiedFormula == sd->getFormula()) {
              return ts;
            }
            return TermList(Term::createFormula(simplifiedFormula));
          }
        }
      }
      case Term::SF_ITE: {
        Formula* condition  = simplify(sd->getCondition());

        #define BRANCH unsigned
        #define THEN 0u
        #define ELSE 1u

        TermList branches[2] = {
          simplify(*term->nthArgument(THEN)),
          simplify(*term->nthArgument(ELSE)),
        };
        bool isTrue[2] {};
        bool isFalse[2] {};

        switch (condition->connective()) {
          case TRUE:
            return branches[THEN];
          case FALSE:
            return branches[ELSE];
          default:
            break;
        }

        /*
          if C then 1 else B  to  C | B
          if C then 0 else B  to ~C & B
          if C then A else 1  to ~C | A
          if C then A else 0  to  C & A
         */
        for (BRANCH branch : { THEN, ELSE }) {
          bool isTerm = branches[branch].isTerm();
          isTrue[branch]  = isTerm && env.signature->isFoolConstantSymbol(true,  branches[branch].term()->functor());
          isFalse[branch] = isTerm && env.signature->isFoolConstantSymbol(false, branches[branch].term()->functor());
        }

        for (BRANCH branch : {THEN, ELSE }) {
          if (isTrue[branch] || isFalse[branch]) {
            Formula* f = (isFalse[THEN] || isTrue[ELSE]) ? (Formula*) new NegatedFormula(condition) : condition;
            BRANCH counterpart = branch == THEN ? ELSE : THEN;
            if (isTrue[counterpart] || isFalse[counterpart]) {
              if (isTrue[branch] == isTrue[counterpart]) {
                return TermList(isTrue[branch] ? Term::foolTrue() : Term::foolFalse());
              } else {
                return TermList(Term::createFormula(f));
              }
            } else {
              Formula* counterpartFormula = BoolTermFormula::create(branches[counterpart]);
              FormulaList* args = new FormulaList(f, new FormulaList(counterpartFormula));
              Formula* junction = new JunctionFormula(isTrue[branch] ? OR : AND, args);
              return TermList(Term::createFormula(junction));
            }
          }
        }

        if ((condition  == sd->getCondition()) &&
            (branches[THEN] == *term->nthArgument(THEN)) &&
            (branches[ELSE] == *term->nthArgument(ELSE))) {
          return ts;
        }
        TermList sort = sd->getSort();
        return TermList(Term::createITE(condition, branches[THEN], branches[ELSE], sort));
      }
      case Term::SF_LET: {
        unsigned functor = sd->getFunctor();
        VList* variables = sd->getVariables();
        TermList binding = simplify(sd->getBinding());
        TermList body = simplify(*term->nthArgument(0));
        if ((binding == sd->getBinding()) && (body == *term->nthArgument(0))) {
          return ts;
        }
        TermList sort = sd->getSort();
        return TermList(Term::createLet(functor, variables, binding, body, sort));
      }
      case Term::SF_LET_TUPLE: {
        unsigned functor = sd->getFunctor();
        VList* symbols = sd->getTupleSymbols();
        TermList binding = simplify(sd->getBinding());
        TermList body = simplify(*term->nthArgument(0));
        if ((binding == sd->getBinding()) && (body == *term->nthArgument(0))) {
          return ts;
        }
        TermList sort = sd->getSort();
        return TermList(Term::createLet(functor, symbols, binding, body, sort));
      }
      case Term::SF_TUPLE: {
        TermList tupleTerm = TermList(sd->getTupleTerm());
        TermList simplifiedTupleTerm = simplify(tupleTerm);
        if (tupleTerm == simplifiedTupleTerm) {
          return ts;
        }
        ASS_REP(simplifiedTupleTerm.isTerm(), simplifiedTupleTerm.toString());
        return TermList(Term::createTuple(simplifiedTupleTerm.term()));
      }
      case Term::SF_MATCH: {
        DArray<TermList> terms(term->arity());
        bool unchanged = true;
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = simplify(*term->nthArgument(i));
          unchanged = unchanged && (terms[i] == *term->nthArgument(i));
        }

        if (unchanged) {
          return ts;
        }
        return TermList(Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin()));
      }
      default:
        ASSERTION_VIOLATION_REP(term->toString());
    }
  }

  bool simplified = false;
  Stack<TermList> arguments;
  Term::Iterator it(term);
  while (it.hasNext()) {
    TermList argument = it.next();
    TermList simplifiedArgument = simplify(argument);
    if (argument != simplifiedArgument) {
      simplified = true;
    }
    arguments.push(simplifiedArgument);
  }

  if (!simplified) {
    return ts;
  }
  
  return TermList(Term::create(term, arguments.begin()));
} // SimplifyFalseTrue::simplify(TermList)
