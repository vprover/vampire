/**
 * @file Skolem.cpp
 * Implementing Skolemisation.
 * @since 05/01/2003 Manchester
 * @since 08/07/2007 flight Manchester-Cork, changed to new datastructures
 */

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "Rectify.hpp"
#include "Skolem.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Skolemise the unit.
 *
 * @warning the unit must contain a closed formula in NNF
 * @since 05/01/2004 Manchester
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 31/01/2004 Manchester. Rectify inference has been added
 * (otherwise proof-checking had been very difficult).
 */
Unit* Skolem::skolemise (Unit* unit)
{
  CALL("Skolem::skolemise(Unit*)");
  ASS(! unit->isClause());

  unit = Rectify::rectify(unit);
  Formula* f = static_cast<FormulaUnit*>(unit)->formula();
  switch (f->connective()) {
  case FALSE:
  case TRUE:
    return unit;
  default:
    break;
  }

  Skolem skol;
  skol._beingSkolemised=unit;
  Formula* g = skol.skolemise(f);
  if (f == g) { // not changed
    return unit;
  }
  return new FormulaUnit(g,
			 new Inference1(Inference::SKOLEMIZE,unit),
			 unit->inputType());
} // Skolem::skolemise

/**
 * Skolemise a subformula.
 *
 * @param f the subformula
 *
 * @since 28/06/2002 Manchester
 * @since 04/09/2002 Bolzano, changed
 * @since 05/09/2002 Trento, changed
 * @since 19/01/2002 Manchester, information about 
 *        positions and inferences added.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 31/01/2004 Manchester, simplified to work with rectified formulas
 * @since 11/12/2004 Manchester, true and false added
 * @since 12/12/2004 Manchester, optimised by quantifying only over
 *    variables actually occurring in the formula.
 * @since 28/12/2007 Manchester, changed to new datastructures
 */
Formula* Skolem::skolemise (Formula* f)
{
  CALL("Skolem::skolemise (Formula*)");

  switch (f->connective()) {
  case LITERAL: 
    {
      Literal* l = f->literal();
      Literal* ll = l->apply(_subst);
      if (l == ll) {
	return f;
      }
      return new AtomicFormula(ll);
    }

  case AND:
  case OR: 
    {
      FormulaList* fs = skolemise(f->args());
      if (fs == f->args()) {
	return f;
      }
      return new JunctionFormula(f->connective(),fs);
    }

  case FORALL: 
    {
      int ln = _vars.length();
      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
	_vars.push(vs.next());
      }
      Formula* g = skolemise(f->qarg());
      _vars.truncate(ln);
      if (g == f->qarg()) {
	return f;
      }
      return new QuantifiedFormula(f->connective(),f->vars(),g);
    }

  case EXISTS: 
    {
      int arity = _vars.length();

      //the skolem functions are now transparent
//      Color clr=COLOR_TRANSPARENT;
      //Color clr=f->qarg()->getColor();
      /*if(clr!=COLOR_TRANSPARENT) {
	//if there are colored predicate symbols, we want it to be transparent
	SubformulaIterator si(f);
	while(si.hasNext()) {
	  Formula* f=si.next();
	  if(f->connective()!=LITERAL) {
	    continue;
	  }
	  Literal* lit=f->literal();
	  if(lit->color()!=COLOR_TRANSPARENT && env.signature->getPredicate(lit->functor())->color()!=COLOR_TRANSPARENT) {
	    clr=COLOR_TRANSPARENT;
	    cout<<"transparent ";
	    break;
	  }
	}
      }*/

      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
	int v = vs.next();
	unsigned fun = env.signature->addSkolemFunction(arity);
//	if(clr!=COLOR_TRANSPARENT) {
//	  env.signature->getFunction(fun)->addColor(clr);
//	}
	Term* term = new(arity) Term;
	term->makeSymbol(fun,arity);
	TermList* args = term->args();
	for (int i = arity-1;i >= 0;i--) {
	  args->makeVar(_vars[i]);
	  args = args->next();
	}
	_subst.bind(v,env.sharing->insert(term));

	if(env.options->showSkolemisations()) {
	  env.beginOutput();
	  env.out()<<"Skolemising: "<<term->toString()<<" for X"<<v<<" in "<<f->toString()<<" in formula "<<_beingSkolemised->toString()<<endl;
	  env.endOutput();
//	  //we also output skolemisations in a TPTP format to the error output
//	  cerr<<term->toString()<<"=X"<<v<<" => ("<<f->qarg()->toString()<<")"<<endl;
	}
      }
      Formula* g = skolemise(f->qarg());
      vs.reset(f->vars());
      while (vs.hasNext()) {
	_subst.unbind(vs.next());
      }
      _vars.truncate(arity);

      return g;
    }

  case TRUE:
  case FALSE:
    return f;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
} // Skolem::skolemise


/**
 * Skolemise a list of formulas in NFF.
 *
 * @since 28/06/2002 Manchester
 * @since 04/09/2002 Bolzano, changed
 * @since 19/01/2002 Manchester, information about 
 *        positions and inferences added.
 * @since 23/01/2004 Manchester, changed to use non-static functions
 * @since 12/12/2004 Manchester, optimised by quantifying only over
 *    variables actually occurring in the formula.
 */
FormulaList* Skolem::skolemise (FormulaList* fs) 
{
  CALL("skolemise (FormulaList*)");

  if (fs->isEmpty()) {
    return fs;
  }

  Formula* g = fs->head();
  FormulaList* gs = fs->tail();
  Formula* h = skolemise(g);
  FormulaList* hs = skolemise(gs);

  if (gs == hs && g == h) {
    return fs;
  }
  return new FormulaList(h,hs);
} // Skolem::skolemise


