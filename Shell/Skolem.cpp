/**
 * @file Skolem.cpp
 * Implementing Skolemisation.
 * @since 05/01/2003 Manchester
 * @since 08/07/2007 flight Manchester-Cork, changed to new datastructures
 */

#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/TermIterators.hpp"

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
  return skol.skolemiseImpl(unit);
} // Skolem::skolemise

FormulaUnit* Skolem::skolemiseImpl (FormulaUnit* unit)
{
  CALL("Skolem::skolemiseImpl(FormulaUnit*)");

  ASS(_introducedSkolemFuns.isEmpty());

  _beingSkolemised=unit;

  _skolimizingDefinitions = UnitList::empty();

  _vars.reset();
  _varSorts.reset();
  _subst.reset();

  Formula* f = unit->formula();
  preskolemise(f);
  ASS_EQ(_vars.size(),0);

  Formula* g = skolemise(f);

  _beingSkolemised = 0;

  if (f == g) { // not changed
    return unit;
  }

  UnitList* premiseList = new UnitList(unit,_skolimizingDefinitions);

  Inference* inf = new InferenceMany(Inference::SKOLEMIZE,premiseList);
  FormulaUnit* res = new FormulaUnit(g, inf, unit->inputType());

  ASS(_introducedSkolemFuns.isNonEmpty());
  while(_introducedSkolemFuns.isNonEmpty()) {
    unsigned fn = _introducedSkolemFuns.pop();
    InferenceStore::instance()->recordIntroducedSymbol(res,true,fn);
  }

  return res;
}

unsigned Skolem::addSkolemFunction(unsigned arity, unsigned* domainSorts,
    unsigned rangeSort, unsigned var)
{
  CALL("Skolem::addSkolemFunction(unsigned,unsigned*,unsigned,unsigned)");

  if(VarManager::varNamePreserving()) {
    vstring varName=VarManager::getVarName(var);
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

void Skolem::ensureHavingVarSorts()
{
  CALL("Skolem::ensureHavingVarSorts");

  if (_varSorts.size() == 0) {
    Formula* f = _beingSkolemised->formula();
    SortHelper::collectVariableSorts(f, _varSorts);
  }
}

/**
 * Traverse the given formula and prepare skolemising
 * substitution based actual on occurrences
 * of universal variables in the sub-formulas below
 * existential quantifiers.
 */
void Skolem::preskolemise (Formula* f)
{
  CALL("Skolem::preskolemise (Formula*)");

  switch (f->connective()) {
  case LITERAL:
    {
      const Literal* l = f->literal();

      VariableIterator it(l);
      while (it.hasNext()) {
        TermList v = it.next();
        ASS(v.isVar());
        VarInfo* varInfo;
        if (_vars.find(v.var(),varInfo) && // a universal variable ...
            VarInfo::isNonEmpty(varInfo)) { // ... below an existential quantifier ...
          *varInfo->headPtr() = true; // ... occurs in this literal
        }
      }
      return;
    }

  case AND:
  case OR:
    {
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        preskolemise(it.next());
      }
      return;
    }

  case FORALL:
    {
      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        ALWAYS(_vars.insert(vs.next(),nullptr)); // ALWAYS, because we are rectified
      }
      preskolemise(f->qarg());
      vs.reset(f->vars());
      while (vs.hasNext()) {
        _vars.remove(vs.next());
      }
      return;
    }

  case EXISTS:
    {
      { // reset the "occurs" flag for all the universals we are in scope of
        Vars::Iterator vit(_vars);
        while (vit.hasNext()) {
          unsigned dummy;
          VarInfo*& varInfo = vit.nextRef(dummy);
          VarInfo::push(false,varInfo);
        }
      }
      preskolemise(f->qarg());

      // now create the skolems for the existentials here
      // and bind them in _subst
      unsigned arity = 0;
      ensureHavingVarSorts();
      static Stack<unsigned> domainSorts;
      static Stack<TermList> fnArgs;
      domainSorts.reset();
      fnArgs.reset();

      // for proof recording purposes, see below
      Formula::VarList* var_args = Formula::VarList::empty();
      static Substitution localSubst;
      localSubst.reset();

      Vars::Iterator vit(_vars);
      while(vit.hasNext()) { // TODO: this iterator may present the variables in a "weird" order, consider sorting, for users' sake
        unsigned uvar;
        VarInfo*& varInfo = vit.nextRef(uvar);
        ASS(VarInfo::isNonEmpty(varInfo));
        if (!VarInfo::pop(varInfo)) { // the var didn't really occur in the subformula
          continue;
        }
        if (VarInfo::isNonEmpty(varInfo)) { // pass the fact that it did occur above
          *varInfo->headPtr() = true;
        }
        arity++;
        domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
        fnArgs.push(TermList(uvar, false));
        Formula::VarList::push(uvar,var_args);
      }

      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        int v = vs.next();
        unsigned rangeSort=_varSorts.get(v, Sorts::SRT_DEFAULT);

        unsigned fun = addSkolemFunction(arity, domainSorts.begin(), rangeSort, v);
        _introducedSkolemFuns.push(fun);

        Term* skolemTerm = Term::create(fun, arity, fnArgs.begin());
        _subst.bind(v,skolemTerm);
        localSubst.bind(v,skolemTerm);

        if (env.options->showSkolemisations()) {
          env.beginOutput();
          env.out() << "Skolemising: "<<skolemTerm->toString()<<" for X"<< v
            <<" in "<<f->toString()<<" in formula "<<_beingSkolemised->toString() << endl;
          env.endOutput();
        }

        if (env.options->showNonconstantSkolemFunctionTrace() && arity!=0) {
          env.beginOutput();
          ostream& out = env.out();
            out <<"Nonconstant skolem function introduced: "
            <<skolemTerm->toString()<<" for X"<<v<<" in "<<f->toString()
            <<" in formula "<<_beingSkolemised->toString()<<endl;

          Refutation ref(_beingSkolemised, true);
          ref.output(out);
          env.endOutput();
        }
      }

      {
        Formula* def = new BinaryFormula(IMP, f, SubstHelper::apply(f->qarg(), localSubst));

        if (arity > 0) {
          def = new QuantifiedFormula(FORALL,var_args,nullptr,def);
        }

        Unit* defUnit = new FormulaUnit(def, new Inference(Inference::CHOICE_AXIOM), Unit::AXIOM);
        UnitList::push(defUnit,_skolimizingDefinitions);
      }

      return;
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

  case TRUE:
  case FALSE:
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION;
#endif
  }
}

/**
 * Skolemise a subformula = drop existential quantifiers,
 * and apply already prepared substitution in literals.
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
 * @since 14/11/2015 Manchester, changed to really optimise by quantifying only over
 *    variables actually occurring in the formula (done in cooperation with preskolimise)
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
      Formula* g = skolemise(f->qarg());
      if (g == f->qarg()) {
        return f;
      }
      return new QuantifiedFormula(f->connective(),f->vars(),f->sorts(),g);
    }

  case EXISTS: 
    {
      // drop the existential one:
      return skolemise(f->qarg());
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

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

  if (FormulaList::isEmpty(fs)) {
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


