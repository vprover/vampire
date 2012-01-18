/**
 * @file NNF.cpp
 * Implements NNF-related transformations.
 * @since 28/12/2003 Manchester
 */

#include "Lib/Environment.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"

#include "Indexing/TermSharing.hpp"

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

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  Formula* g = ennf(f,true);
  if (f == g) { // not changed
    return unit;
  }

  return new FormulaUnit(g,
			 new Inference1(Inference::ENNF,unit),
			 unit->inputType());
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

  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  Formula* g = nnf(f,true);
  if (f == g) { // not changed
    return unit;
  }

  return new FormulaUnit(g,
			 new Inference1(Inference::NNF,unit),
			 unit->inputType());
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
      FormulaList* gs = ennf(fs,polarity);
      if (fs == gs) {
	ASS(polarity);
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
	ASS(polarity);
	return f;
      }
      if (polarity) {
	return new QuantifiedFormula(c,f->vars(),gg);
      }
      return new QuantifiedFormula(c == EXISTS ? FORALL : EXISTS,
				   f->vars(),gg);
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
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // NNF::ennf(Formula&);


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

  if (fs->isEmpty()) {
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
  result->destroy();
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
	return new QuantifiedFormula(c,f->vars(),gg);
      }
      return new QuantifiedFormula(c == EXISTS ? FORALL : EXISTS,
				   f->vars(),gg);
    }

  case TRUE:
  case FALSE:
    return f;
#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
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

  if (fs->isEmpty()) {
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
  result->destroy();
  return fs;
} // NNF::nnf(FormulaList...)


