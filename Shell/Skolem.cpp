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
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"

#include "Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "Rectify.hpp"
#include "Refutation.hpp"
#include "Skolem.hpp"
#include "VarManager.hpp"

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
FormulaUnit* Skolem::skolemise (FormulaUnit* unit)
{
  CALL("Skolem::skolemise(Unit*)");
  ASS(! unit->isClause());

  unit = Rectify::rectify(unit);
  Formula* f = unit->formula();
  switch (f->connective()) {
  case FALSE:
  case TRUE:
    return unit;
  default:
    break;
  }

  static Skolem skol;
  skol.reset();
  return skol.skolemiseImpl(unit);
} // Skolem::skolemise

FormulaUnit* Skolem::skolemiseImpl (FormulaUnit* unit)
{
  CALL("Skolem::skolemiseImpl(FormulaUnit*)");

  _beingSkolemised=unit;

  Formula* f = unit->formula();
  SortHelper::collectVariableSorts(f, _varSorts);

  Formula* g = skolemise(f);
  if (f == g) { // not changed
    return unit;
  }
  return new FormulaUnit(g,
			 new Inference1(Inference::SKOLEMIZE,unit),
			 unit->inputType());
}


void Skolem::reset()
{
  CALL("Skolem::reset");

  _vars.reset();
  _varSorts.reset();
  _subst.reset();
}

unsigned Skolem::addSkolemFunction(unsigned arity, unsigned* domainSorts,
    unsigned rangeSort, unsigned var)
{
  CALL("Skolem::addSkolemFunction(unsigned,unsigned*,unsigned,unsigned)");

  if(VarManager::varNamePreserving()) {
    string varName=VarManager::getVarName(var);
    return addSkolemFunction(arity, domainSorts, rangeSort, varName.c_str());
  }
  else {
    return addSkolemFunction(arity, domainSorts, rangeSort);
  }
}

unsigned Skolem::addSkolemFunction(unsigned arity, unsigned* domainSorts,
    unsigned rangeSort, const char* suffix)
{
  CALL("Skolem::addSkolemFunction(unsigned,unsigned*,unsigned,const char*)");
  ASS(arity==0 || domainSorts!=0);

  unsigned fun = env.signature->addSkolemFunction(arity, suffix);
  Signature::Symbol* fnSym = env.signature->getFunction(fun);
  fnSym->setType(new FunctionType(arity, domainSorts, rangeSort));
  return fun;
}

Term* Skolem::createSkolemTerm(unsigned var)
{
  CALL("Skolem::createSkolemFunction");

  int arity = _vars.length();

  unsigned rangeSort=_varSorts.get(var, Sorts::SRT_DEFAULT);
  static Stack<unsigned> domainSorts;
  static Stack<TermList> fnArgs;
  domainSorts.reset();
  fnArgs.reset();

  VarStack::TopFirstIterator vit(_vars);
  while(vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
    fnArgs.push(TermList(uvar, false));
  }

  unsigned fun = addSkolemFunction(arity, domainSorts.begin(), rangeSort, var);

  return Term::create(fun, arity, fnArgs.begin());
}

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

      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
	int v = vs.next();
	Term* skolemTerm = createSkolemTerm(v);
	_subst.bind(v,skolemTerm);

	if(env.options->showSkolemisations()) {
	  env.beginOutput();
	  env.out()<<"Skolemising: "<<skolemTerm->toString()<<" for X"<<v<<" in "<<f->toString()<<" in formula "<<_beingSkolemised->toString()<<endl;
	  env.endOutput();
	}
	if(arity!=0 && env.options->showNonconstantSkolemFunctionTrace()) {
	  cerr<<"Nonconstant skolem function introduced: "<<skolemTerm->toString()<<" for X"<<v<<" in "<<f->toString()<<" in formula "<<_beingSkolemised->toString()<<endl;
	  Refutation ref(_beingSkolemised, true);
	  ref.output(cerr);
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


