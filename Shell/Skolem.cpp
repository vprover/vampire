
/*
 * File Skolem.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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
#include "Lib/SharedSet.hpp"

#include "Shell/Statistics.hpp"

#include "Indexing/TermSharing.hpp"

#include "Options.hpp"
#include "Rectify.hpp"
// #include "Refutation.hpp"
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

  _varOccs.reset();
  _varSorts.reset();
  _subst.reset();
  _varDeps.reset();
  _blockLookup.reset();

  Formula* f = unit->formula();
  preskolemise(f);
  ASS_EQ(_varOccs.size(),0);

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
    if(unit->isGoal()){
      env.signature->getFunction(fn)->markInGoal();
    }
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
  fnSym->setType(OperatorType::getFunctionType(arity, domainSorts, rangeSort));
  return fun;
}

unsigned Skolem::addSkolemPredicate(unsigned arity, unsigned* domainSorts, unsigned var)
{
  CALL("Skolem::addSkolemPredicate(unsigned,unsigned*,unsigned,unsigned)");

  if(VarManager::varNamePreserving()) {
    vstring varName=VarManager::getVarName(var);
    return addSkolemPredicate(arity, domainSorts, varName.c_str());
  }
  else {
    return addSkolemPredicate(arity, domainSorts);
  }
}

unsigned Skolem::addSkolemPredicate(unsigned arity, unsigned* domainSorts, const char* suffix)
{
  CALL("Skolem::addSkolemPredicate(unsigned,unsigned*,unsigned,const char*)");
  ASS(arity==0 || domainSorts!=0);

  unsigned pred = env.signature->addSkolemPredicate(arity, suffix);
  Signature::Symbol* pSym = env.signature->getPredicate(pred);
  pSym->setType(OperatorType::getPredicateType(arity, domainSorts));
  return pred;
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
        VarOccInfo varOccInfo;
        ALWAYS(_varOccs.find(v.var(),varOccInfo));

        if (BoolList::isNonEmpty(varOccInfo.occurs_below)) { // below a quantifier ...
          varOccInfo.occurs_below->headRef() = true;         // ... occurs in this literal
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
        ALWAYS(_varOccs.insert(vs.next(),{false/*univeral*/,nullptr})); // ALWAYS, because we are rectified
      }
      preskolemise(f->qarg());
      vs.reset(f->vars());
      while (vs.hasNext()) {
        _varOccs.remove(vs.next());
      }
      return;
    }

  case EXISTS:
    {
      { // reset the "occurs" flag for all the variables we are in scope of
        VarOccInfos::Iterator vit(_varOccs);
        while (vit.hasNext()) {
          unsigned dummy;
          VarOccInfo& varOccInfo = vit.nextRef(dummy);
          BoolList::push(false,varOccInfo.occurs_below);
        }
      }

      // add our own variables (for which we are not interested in occurrences)
      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        unsigned var = vs.next();
        ALWAYS(_varOccs.insert(var,{true/*existential*/,nullptr})); // ALWAYS, because we are rectified
        ALWAYS(_blockLookup.insert(var,f));
      }

      preskolemise(f->qarg());

      // take ours out again
      vs.reset(f->vars());
      while (vs.hasNext()) {
        _varOccs.remove(vs.next());
      }

      static Stack<unsigned> univ_dep_stack;
      static Stack<unsigned> exists_deps_stack;
      ASS(univ_dep_stack.isEmpty());
      ASS(exists_deps_stack.isEmpty());

      // collect results from subformulas
      VarOccInfos::Iterator vit(_varOccs);
      while(vit.hasNext()) {
        unsigned var;
        VarOccInfo& varOccInfo = vit.nextRef(var);
        ASS(BoolList::isNonEmpty(varOccInfo.occurs_below));
        if (!BoolList::pop(varOccInfo.occurs_below)) { // the var didn't really occur in the subformula
          continue;
        }
        if (BoolList::isNonEmpty(varOccInfo.occurs_below)) { // pass the fact that it did occur above
          varOccInfo.occurs_below->headRef() = true;
        }

        if (varOccInfo.existential) {
          exists_deps_stack.push(var);
        } else {
          univ_dep_stack.push(var);
        }
      }

      Stack<unsigned>::Iterator udIt(univ_dep_stack);
      VarSet* univ_dep_set = VarSet::getFromIterator(udIt);
      univ_dep_stack.reset();

      Stack<unsigned>::Iterator edIt(exists_deps_stack);
      VarSet* exists_dep_set = VarSet::getFromIterator(edIt);
      exists_deps_stack.reset();

      _varDeps.insert(f,{univ_dep_set,exists_dep_set});

      return;
    }

  case BOOL_TERM:
    ASSERTION_VIOLATION;

  case TRUE:
  case FALSE:
    return;

#if VDEBUG
  default:
    ASSERTION_VIOLATION_REP(f->connective());
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
      // create the skolems for the existentials here
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

      ExVarDepInfo& depInfo = _varDeps.get(f);

      VarSet* dep = depInfo.univ;

      VarSet::Iterator veIt(*depInfo.exist);
      while(veIt.hasNext()) {
        unsigned evar = veIt.next();
        Formula* block = _blockLookup.get(evar);
        VarSet* their_dep = _varDeps.get(block).univ;
        dep = dep->getUnion(their_dep);
      }

      /*
      if (depInfo.univ != dep) {
        // PANIC !!!
      }
      */

      // store updated, for the existentials below us to lookup as well
      depInfo.univ = dep;

      VarSet::Iterator vuIt(*dep);
      while(vuIt.hasNext()) {
        unsigned uvar = vuIt.next();
        domainSorts.push(_varSorts.get(uvar, Sorts::SRT_DEFAULT));
        fnArgs.push(TermList(uvar, false));
        Formula::VarList::push(uvar,var_args);
        arity++;
      }

      Formula::VarList::Iterator vs(f->vars());
      while (vs.hasNext()) {
        int v = vs.next();
        unsigned rangeSort=_varSorts.get(v, Sorts::SRT_DEFAULT);

        unsigned fun = addSkolemFunction(arity, domainSorts.begin(), rangeSort, v);
        _introducedSkolemFuns.push(fun);

        env.statistics->skolemFunctions++;

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

          /*
          Refutation ref(_beingSkolemised, true);
          ref.output(out);
          */
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
  CALL("Skolem:skolemise(FormulaList*)");

  ASS(FormulaList::isNonEmpty(fs));

  Stack<FormulaList*> args;

  while (FormulaList::isNonEmpty(fs)) {
    args.push(fs);
    fs = fs->tail();
  }

  FormulaList* res = args.top()->tail();
  ASS(FormulaList::isEmpty(res));

  while (args.isNonEmpty()) {
    fs = args.pop();
    Formula* g = fs->head();
    FormulaList* gs = fs->tail();
    Formula* h = skolemise(g);
    FormulaList* hs = res; // = skolemise(gs);

    if (gs == hs && g == h) {
      res = fs;
    } else {
      res = new FormulaList(h,hs);
    }
  }

  return res;
} // Skolem::skolemise


