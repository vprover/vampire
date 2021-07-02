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
 * @file NNF.cpp
 * Implements NNF-related transformations.
 * @since 28/12/2003 Manchester
 */

#include "Lib/Environment.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Options.hpp"

#include "NNF.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Transform the unit into ENNF.
 * @since 28/12/2003 Manchester
 * @warning the unit must contain a formula
 * @since 27/06/2007 Flight Frankfurt-Paris, changed to use new data structures
 */
FormulaUnit* NNF::ennf(FormulaUnit* unit)
{
  CALL("NNF::ennf(Unit* u)");
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = ennf(f,true);
  if (f == g) { // not changed
    return unit;
  }

  FormulaUnit* res = new FormulaUnit(g,FormulaTransformation(InferenceRule::ENNF,unit));

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] ennf in: " << unit->toString() << std::endl;
    env.out() << "[PP] ennf out: " << res->toString() << std::endl;
    env.endOutput();
  }

  return res;
} // NNF::ennf


/**
 * Transform the unit into NNF.
 * @since 29/12/2003 Manchester
 * @warning the unit must contain a formula
 * @since 27/06/2007 Flight Frankfurt-Paris, changed to use new data structures
 */
FormulaUnit* NNF::nnf(FormulaUnit* unit)
{
  CALL("NNF::nnf(Unit*)");
  ASS(! unit->isClause());

  Formula* f = unit->formula();
  Formula* g = nnf(f,true);
  if (f == g) { // not changed
    return unit;
  }

  return new FormulaUnit(g,FormulaTransformation(InferenceRule::NNF,unit));
} // NNF::nnf


/**
 * Transform f or its negation into ennf. 
 *
 * @param f the formula
 * @param polarity if false, then the negation of f should
 *        be transformed
 *
 * @since 12/05/2002 Manchester
 * @since 30/08/2002 Torrevieja, changed
 * @since 28/12/2003 Manchester, simplified by removing flattening-related
 *                   steps
 * @since 22/01/2004 Manchester, info anout inference and position added
 * @since 11/12/2004 Manchester, true and false added
 * @since 27/06/2007 Flight Frankfurt-Paris, changed to use new data structures
 */
Formula* NNF::ennf (Formula* f, bool polarity)
{
  CALL("NNF::ennf(Formula*...)");

  Connective c = f->connective();
  switch (c) {
  case LITERAL:
    {
      Literal* lit = f->literal();

      // in general, it does not make sense to propagate polarity to literals
      // (the only sensible special case would be, if the literal was actually a special term of type formula, but newcnf will cope if we don't "polarify" these)
      Literal* newLit = ennf(lit);

      // take polarity into account here
      newLit = polarity ? newLit : Literal::complementaryLiteral(newLit);

      if (newLit == lit) {
        return f;
      } else {
        return new AtomicFormula(newLit);
      }
    }

  case AND: 
  case OR: 
    {
      FormulaList* fs = f->args();
      FormulaList* gs = ennf(fs,polarity);
      if (fs == gs) {
	return f;
      }
      if (polarity) {
 	return new JunctionFormula(c,gs);
      }
      return new JunctionFormula(c == AND ? OR : AND,gs);
    }
      
  case IMP: 
    {
      Formula* l = ennf(f->left(),! polarity);
      Formula* r = ennf(f->right(),polarity);
      FormulaList* args = new FormulaList(l,new FormulaList(r));
      return new JunctionFormula(polarity ? OR : AND,args);
    }
    
  case IFF: 
  case XOR: 
    {
      Formula* l = f->left();
      Formula* r = f->right();
      Formula* ll = ennf(l,true);
      Formula* rr = ennf(r,true);
      if (polarity) {
	if (l == ll && r == rr) { // nothing has changed
	  return f;
	}
	return new BinaryFormula(c, ll, rr);
      }
      return new BinaryFormula(c == XOR ? IFF : XOR, ll, rr);
    }

    case NOT:
      return ennf(f->uarg(),!polarity);

  case FORALL:
  case EXISTS: 
    {
      Formula* g = f->qarg();
      Formula* gg = ennf(g,polarity);
      if (g == gg) {
	return f;
      }
      if (polarity) {
	return new QuantifiedFormula(c,f->vars(),f->sorts(),gg);
      }
      return new QuantifiedFormula(c == EXISTS ? FORALL : EXISTS,
				   f->vars(),f->sorts(),gg);
    }

  case BOOL_TERM: {
    TermList ts = f->getBooleanTerm();
    TermList ennfTf = ennf(ts, polarity);
    if (ts == ennfTf) {
      if (polarity) {
        return f;
      } else {
        return new NegatedFormula(f);
      }
    } else {
      return new BoolTermFormula(ennfTf);
    }
  }

  case TRUE:
  case FALSE:
    if(polarity) {
      return f;
    }
    else {
      if(c==TRUE) {
	return Formula::falseFormula();
      }
      else {
	return Formula::trueFormula();
      }
    }
  default:
    ASSERTION_VIOLATION;
  }
} // NNF::ennf(Formula&);

Literal* NNF::ennf(Literal* l)
{
  CALL("NNF::ennf(Literal*...)");

  if (l->shared()) {
    return l;
  }

  bool changed = false;
  Stack<TermList> args;
  Term::Iterator terms(l);
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList ennfArgument = ennf(argument, true);
    if (argument != ennfArgument) {
      changed = true;
    }
    args.push(ennfArgument);
  }

  if (!changed) {
    return l;
  }

  return Literal::create(l, args.begin());
} // NNF::ennf(Literal*);

TermList NNF::ennf(TermList ts, bool polarity)
{
  CALL("NNF::ennf(TermList...)");

  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();

  if (env.signature->isFoolConstantSymbol(true, term->functor())) {
    return polarity ? ts : TermList(Term::foolFalse());
  }

  if (env.signature->isFoolConstantSymbol(false, term->functor())) {
    return polarity ? ts : TermList(Term::foolTrue());
  }

  if (term->shared()) {
    return ts;
  }

  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        Formula* f = sd->getFormula();
        Formula* ennfF = ennf(f, polarity);
        switch (ennfF->connective()) {
          case TRUE:
            return TermList(Term::foolTrue());
          case FALSE:
            return TermList(Term::foolFalse());
          default: {
            if (f == ennfF) {
              return ts;
            } else {
              return TermList(Term::createFormula(ennfF));
            }
          }
        }
        break;
      }

      case Term::SF_ITE: {
        TermList thenBranch = *term->nthArgument(0);
        TermList elseBranch = *term->nthArgument(1);
        Formula* condition  = sd->getCondition();

        TermList ennfThenBranch = ennf(thenBranch, polarity);
        TermList ennfElseBranch = ennf(elseBranch, polarity);
        Formula* ennfCondition  = ennf(condition, true);

        if ((thenBranch == ennfThenBranch) &&
            (elseBranch == ennfElseBranch) &&
            (condition == ennfCondition)) {
          return ts;
        } else {
          return TermList(Term::createITE(ennfCondition, ennfThenBranch, ennfElseBranch, sd->getSort()));
        }
        break;
      }

      case Term::SF_LET: {
        TermList binding = sd->getBinding();
        TermList body = *term->nthArgument(0);

        TermList ennfBinding = ennf(binding, true);
        TermList ennfBody = ennf(body, polarity);

        if ((binding == ennfBinding) && (body == ennfBody)) {
          return ts;
        } else {
          return TermList(Term::createLet(sd->getFunctor(), sd->getVariables(), ennfBinding, ennfBody, sd->getSort()));
        }
        break;
      }

      case Term::SF_LET_TUPLE: {
        TermList binding = sd->getBinding();
        TermList body = *term->nthArgument(0);

        TermList ennfBinding = ennf(binding, true);
        TermList ennfBody = ennf(body, polarity);

        if ((binding == ennfBinding) && (body == ennfBody)) {
          return ts;
        } else {
          return TermList(Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), ennfBinding, ennfBody, sd->getSort()));
        }
        break;
      }

      case Term::SF_TUPLE: {
        TermList tupleTerm = TermList(sd->getTupleTerm());
        TermList ennfTupleTerm = ennf(tupleTerm, true);

        if (tupleTerm == ennfTupleTerm) {
          return ts;
        } else {
          ASS_REP(ennfTupleTerm.isTerm(), ennfTupleTerm.toString());
          return TermList(Term::createTuple(ennfTupleTerm.term()));
        }
        break;
      }

      case Term::SF_MATCH: {
        DArray<TermList> terms(term->arity());
        bool unchanged = true;
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = ennf(*term->nthArgument(i), polarity);
          unchanged = unchanged && (terms[i] == *term->nthArgument(i));
        }

        if (unchanged) {
          return ts;
        }
        return TermList(Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin()));
      }

      default:
        ASSERTION_VIOLATION;
    }
  }

  bool changed = false;
  Stack<TermList> args;
  Term::Iterator terms(term);
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList ennfArgument = ennf(argument, true);
    if (argument != ennfArgument) {
      changed = true;
    }
    args.push(ennfArgument);
  }

  if (!changed) {
    return ts;
  }

  return TermList(Term::create(term, args.begin()));
} // NNF::ennf(Term*);

/**
 * Transform a junction F = F0 * ... * Fk or its negation into ennf.
 *
 * @param fs the list Fn ... Fk
 * @param polarity if false, then the negation of the formula should
 *        be transformed
 * @returns the list Gn ... Gk such that Gi is NNF of Fi
 *
 * @since 12/05/2002 Manchester
 * @since 30/08/2002 Torrevieja, changed
 * @since 28/12/2003 Manchester, simplified by removing flattening-related
 *                   steps
 * @since 22/01/2004 Manchester, info about inference and position added
 */
FormulaList* NNF::ennf (FormulaList* fs, bool polarity)
{
  CALL("NNF::ennf(FormulaList*...)");

  if (FormulaList::isEmpty(fs)) {
    return fs;
  }

  FormulaList* result = FormulaList::empty();
  FormulaList::FIFO stack(result);
  bool changed = false;
  FormulaList::Iterator it(fs);
  while (it.hasNext()) {
    Formula* f = it.next();
    Formula* g = ennf(f,polarity);
    stack.push(g);
    if (f != g) {
      changed = true;
    }
  }
  if (changed) {
    return result;
  }
  FormulaList::destroy(result);
  return fs;
} // NNF::ennf(FormulaList...)


/**
 * Transform f or its negation into nnf. 
 *
 * @param f the formula
 * @param polarity if false, then the negation of f should
 *        be transformed
 *        ~f, if polarity=false
 *
 * @since 29/12/2003 Manchester
 * @since 26/01/2004 Manchester, info anout inference and position added
 * @since 11/12/2004 Manchester, true and false added
 */
Formula* NNF::nnf (Formula* f, bool polarity)
{
  CALL("NNF::nnf(Formula*...)");

  Connective c = f->connective();
  switch (c) {
  case LITERAL:
    if (! polarity) {
      Literal* lit = f->literal();
      Literal* newLit = Literal::complementaryLiteral(lit);
      return new AtomicFormula(newLit);
    }
    return f;

  case AND: 
  case OR: 
    {
      FormulaList* fs = f->args();
      FormulaList* gs = nnf(fs,polarity);
      if (fs == gs) {
	return f;
      }
      if (polarity) {
	return new JunctionFormula(c,gs);
      }
      return new JunctionFormula(c == AND ? OR : AND,gs);
    }
      
  case IMP: 
    {
      Formula* l = nnf(f->left(),! polarity);
      Formula* r = nnf(f->right(),polarity);
      FormulaList* args = new FormulaList(l,new FormulaList(r));
      return new JunctionFormula(polarity ? OR : AND,args);
    }
    
  case IFF: 
  case XOR: 
    {
      Formula* l = f->left();
      Formula* r = f->right();
      Formula* g;

      if (polarity ? c == IFF : c == XOR) {
	// essentially l <=> r
	// replace f by (l => r) & (r => l) and apply NNF to it
	g = new JunctionFormula(AND,
				new FormulaList(new BinaryFormula(IMP,l,r),
						new FormulaList(new BinaryFormula(IMP,r,l))));
      }
      else {
	// essentially l XOR r
	// replace f by (l \/ r) & (~l \/ ~r) and apply NNF to it
	g = new JunctionFormula(AND,
				new FormulaList(new JunctionFormula(OR,
								    new FormulaList(l,
										    new FormulaList(r))),
						new FormulaList(new JunctionFormula(OR,
										    new FormulaList(new NegatedFormula(l),
												    new FormulaList(new NegatedFormula(r)))))));
      }
      return nnf(g,true);
    }

    case NOT:
      return nnf(f->uarg(),!polarity);

  case FORALL:
  case EXISTS: 
    {
      Formula* g = f->qarg();
      Formula* gg = nnf(g,polarity);

      if (g == gg) {
	ASS(polarity);
	return f;
      }
      if (polarity) {
	return new QuantifiedFormula(c,f->vars(),f->sorts(),gg);
      }
      return new QuantifiedFormula(c == EXISTS ? FORALL : EXISTS,
				   f->vars(),f->sorts(),gg);
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

  case TRUE:
  case FALSE:
    return f;

  case NAME:
  case NOCONN:
    ASSERTION_VIOLATION;
  }

  ASSERTION_VIOLATION;
} // NNF::nnf(Formula*);


/**
 * Transform a junction F = F0 * ... * Fk or its negation into nnf.
 *
 * @param fs the list Fn ... Fk
 * @param polarity if false, then the negation of the formula should
 *        be transformed
 * @returns the list Gn ... Gk such that Gi is NNF of Fi
 *
 * @since 29/12/2003 Manchester
 * @since 26/01/2004 Manchester, info about inference and position added
 */
FormulaList* NNF::nnf (FormulaList* fs, bool polarity)
{
  CALL("NNF::nnf(FormulaList*...)");

  if (FormulaList::isEmpty(fs)) {
    return fs;
  }

  FormulaList* result = FormulaList::empty();
  FormulaList::FIFO stack(result);
  bool changed = false;
  FormulaList::Iterator it(fs);
  while (it.hasNext()) {
    Formula* f = it.next();
    Formula* g = nnf(f,polarity);
    stack.push(g);
    if (f != g) {
      changed = true;
    }
  }
  if (changed) {
    return result;
  }
  FormulaList::destroy(result);
  return fs;
} // NNF::nnf(FormulaList...)


