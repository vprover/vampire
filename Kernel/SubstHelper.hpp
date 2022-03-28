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
 * @file SubstHelper.hpp
 * Defines class SubstHelper.
 */

#ifndef __SubstHelper__
#define __SubstHelper__

#include "Lib/DArray.hpp"
#include "Lib/Recycler.hpp"

#include "Formula.hpp"
#include "SortHelper.hpp"
#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class SubstHelper
{
public:
  /**
   * Apply a substitution to a term. The substitution is
   * specified by the applicator -- an object with method
   * TermList apply(unsigned var)
   *
   * The specified substitution must be an identity on variables
   * bound inside the formula.
   *
   * This function can handle special terms. Terms that have special
   * terms as subterms will not be shared even if @b noSharing==false.
   */
  template<class Applicator>
  static TermList apply(TermList t, Applicator& applicator, bool noSharing=false)
  {
    CALL("SubstHelper::apply(TermList...)");
    return applyImpl<false,Applicator>(t, applicator, noSharing);
  }

  /**
   * Apply a substitution to a term. The substitution is
   * specified by the applicator -- an object with method
   * TermList apply(unsigned var)
   *
   * The specified substitution must be an identity on variables
   * bound inside the formula.
   *
   * This function can handle special terms. Terms that have special
   * terms as subterms will not be shared even if @b noSharing==false.
   */
  template<class Applicator>
  static Term* apply(Term* t, Applicator& applicator, bool noSharing=false)
  {
    CALL("SubstHelper::apply(Term*...)");
    return applyImpl<false,Applicator>(t, applicator, noSharing);
  }

  /**
   * Apply a substitution to a literal. The substitution is
   * specified by the applicator -- an object with method
   * TermList apply(unsigned var)
   *
   * The specified substitution must be an identity on variables
   * bound inside the formula.
   *
   * This function can handle special terms. Terms that have special
   * terms as subterms will not be shared even if @b noSharing==false.
   */
  template<class Applicator>
  static Literal* apply(Literal* lit, Applicator& applicator)
  {
    CALL("SubstHelper::apply(Literal*...)");
    Literal* subbedLit = static_cast<Literal*>(apply(static_cast<Term*>(lit),applicator));
    if(subbedLit->isTwoVarEquality()){ //either nothing's changed or variant
      TermList sort = lit->twoVarEqSort();
      TermList newSort = apply(sort, applicator);
      if((sort != newSort)){
        subbedLit = Literal::createEquality(subbedLit->polarity(), *subbedLit->nthArgument(0), *subbedLit->nthArgument(1), newSort);
      }
    }
    return subbedLit;
  }

  /**
   * Apply a substitution to a literal. Substitution is
   * specified by the applicator -- an object with method
   * TermList apply(unsigned var)
   *
   * Variables bound inside the formula must be transformed into other
   * variables by the substitution. These variables will be transformed
   * as well.
   *
   * This function can handle special terms. Terms that have special
   * terms as subterms will not be shared.
   */
  template<class Applicator>
  static Formula* apply(Formula* f, Applicator& applicator)
  {
    CALL("SubstHelper::apply(Formula*...)");
    return applyImpl<false>(f, applicator, false);
  }


  /**
   * Apply a substitution to a literal. The substitution is
   * specified by the applicator -- an object with methods
   * TermList apply(unsigned var) and
   * TermList applyToSpecVar(unsigned specVar).
   */
  template<class Applicator>
  static TermList applySV(TermList t, Applicator& applicator, bool noSharing=false)
  {
    return applyImpl<true,Applicator>(t, applicator, noSharing);
  }
  template<class Applicator>
  static Term* applySV(Term* t, Applicator& applicator, bool noSharing=false)
  {
    return applyImpl<true,Applicator>(t, applicator, noSharing);
  }
  template<class Applicator>
  static Literal* applySV(Literal* lit, Applicator& applicator)
  {
    return static_cast<Literal*>(applySV(static_cast<Term*>(lit),applicator));
  }


  /**
   * Apply a substitution represented by object, that supports
   * just the method TermList apply(TermList t), to a Literal.
   */
  template<class Subst>
  static Literal* applyToLiteral(Literal* lit, Subst subst)
  {
    CALL("SubstHelper::applyToLiteral");
    static DArray<TermList> ts(32);

    int arity = lit->arity();
    ts.ensure(arity);
    int i = 0;
    for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
      ts[i++]=subst.apply(*args);
    }
    return Literal::create(lit,ts.array());
  }

  template<class Map>
  class MapApplicator
  {
  public:
    MapApplicator(Map* map) : _map(map) {}
    TermList apply(unsigned var) {
      TermList res;
      if(!_map->find(var, res)) {
	res = TermList(var, false);
      }
      return res;
    }
  private:
    Map* _map;
  };

  template<class Map>
  static MapApplicator<Map> getMapApplicator(Map* m)
  {
    return MapApplicator<Map>(m);
  }

private:
  template<bool ProcessSpecVars, class Applicator>
  static Term* applyImpl(Term* t, Applicator& applicator, bool noSharing=false);
  template<bool ProcessSpecVars, class Applicator>
  static TermList applyImpl(TermList t, Applicator& applicator, bool noSharing=false);
  template<bool ProcessSpecVars, class Applicator>
  static Formula* applyImpl(Formula* f, Applicator& applicator, bool noSharing);
  template<bool ProcessSpecVars, class Applicator>
  static FormulaList* applyImpl(FormulaList* f, Applicator& applicator, bool noSharing);

  /**
   * Return true iff the @b terms array does not contain any term that cannot be shared
   *
   * Non-shareable is a non-shared proper term or a special variable.
   */
  static bool canBeShared(TermList * terms, size_t len)
  {
    CALL("SubstHelper::anyNonShareable");

    for(unsigned i=0;i<len;i++) {
      TermList trm=terms[i];
      if(trm.isVSpecialVar()||trm.isSpecialVar()||(trm.isTerm()&&!trm.term()->shared())) {
	return false;
      }
    }
    return true;
  }

};

namespace SubstHelper_Aux
{
template<bool ProcessSpecVars>
struct SpecVarHandler
{
};
template<>
struct SpecVarHandler<true>
{
  template<class Applicator>
  static TermList apply(Applicator& a, unsigned specVar) { return a.applyToSpecVar(specVar); }
};
template<>
struct SpecVarHandler<false>
{
  template<class Applicator>
  static TermList apply(Applicator& a, unsigned specVar) { return TermList(specVar, true); }
};
}

/**
 * Apply a substitution to a term. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var) and, if ProcessSpecVars
 * is set to true, also TermList applyToSpecVar(unsigned specVar).
 *
 * If @b trm can be shared and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 *
 * The specified substitution must be an identity on variables
 * bound inside the formula.
 *
 * This function can handle special terms.
 */
template<bool ProcessSpecVars, class Applicator>
TermList SubstHelper::applyImpl(TermList trm, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::applyImpl(TermList...)");

  using namespace SubstHelper_Aux;

  if(trm.isOrdinaryVar()) {
    return applicator.apply(trm.var());
  }
  else if(trm.isSpecialVar()) {
    return SpecVarHandler<ProcessSpecVars>::apply(applicator, trm.var());
  }
  else {
    ASS(trm.isTerm());
    return TermList(applyImpl<ProcessSpecVars>(trm.term(), applicator, noSharing));
  }
}


/**
 * Apply a substitution to a term. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var) and, if ProcessSpecVars
 * is set to true, also TermList applyToSpecVar(unsigned specVar).
 *
 * If @b trm can be shared and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 *
 * The specified substitution must be an identity on variables
 * bound inside the formula.
 *
 * This function can handle special terms.
 * This function can handle the substitution of sorts.
 */
template<bool ProcessSpecVars, class Applicator>
Term* SubstHelper::applyImpl(Term* trm, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::applyImpl(Term*...)");

  using namespace SubstHelper_Aux;

  if(trm->isSpecial()) {
    Term::SpecialTermData* sd = trm->getSpecialData();
    switch(trm->functor()) {
    case Term::SF_ITE:
      return Term::createITE(
    applyImpl<ProcessSpecVars>(sd->getCondition(), applicator, noSharing),
    applyImpl<ProcessSpecVars>(*trm->nthArgument(0), applicator, noSharing),
    applyImpl<ProcessSpecVars>(*trm->nthArgument(1), applicator, noSharing),
          sd->getSort()
    );
    case Term::SF_LET:
      return Term::createLet(
    sd->getFunctor(),
    sd->getVariables(),
    applyImpl<ProcessSpecVars>(sd->getBinding(), applicator, noSharing),
    applyImpl<ProcessSpecVars>(*trm->nthArgument(0), applicator, noSharing),
    sd->getSort()
    );
    case Term::SF_FORMULA:
      return Term::createFormula(
      applyImpl<ProcessSpecVars>(sd->getFormula(), applicator, noSharing)
      );
    case Term::SF_LET_TUPLE:
      return Term::createTupleLet(
        sd->getFunctor(),
        sd->getTupleSymbols(),
        applyImpl<ProcessSpecVars>(sd->getBinding(), applicator, noSharing),
        applyImpl<ProcessSpecVars>(*trm->nthArgument(0), applicator, noSharing),
        sd->getSort()
        );
    case Term::SF_TUPLE:
      return Term::createTuple(applyImpl<ProcessSpecVars>(sd->getTupleTerm(), applicator, noSharing));
    case Term::SF_MATCH: {
      DArray<TermList> terms(trm->arity());
      for (unsigned i = 0; i < trm->arity(); i++) {
        terms[i] = applyImpl<ProcessSpecVars>(*trm->nthArgument(i), applicator, noSharing);
      }
      return Term::createMatch(sd->getSort(), sd->getMatchedSort(), trm->arity(), terms.begin());
    }
    }
    ASSERTION_VIOLATION;
  }

  Stack<TermList*>* toDo;
  Stack<Term*>* terms;
  Stack<bool>* modified;
  Stack<TermList>* args;

  Recycler::get(toDo);
  Recycler::get(terms);
  Recycler::get(modified);
  Recycler::get(args);

  toDo->reset();
  terms->reset();
  modified->reset();
  args->reset();

  modified->push(false);
  toDo->push(trm->args());

  for(;;) {
    TermList* tt=toDo->pop();
    if(tt->isEmpty()) {
      if(terms->isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the topleve term/literal.
        ASS(toDo->isEmpty());
        break;
      }
      Term* orig=terms->pop();
      if(!modified->pop()) {
        args->truncate(args->length() - orig->arity());
        args->push(TermList(orig));
        continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args->top() - (orig->arity()-1);

      bool shouldShare=!noSharing && canBeShared(argLst, orig->arity());

      Term* newTrm;
      if(shouldShare) {
        if(orig->isSort()){
          newTrm=AtomicSort::create(static_cast<AtomicSort*>(orig), argLst);
        } else {
          newTrm=Term::create(orig,argLst);
        }
      }
      else {
        newTrm=Term::createNonShared(orig,argLst);
      }
      args->truncate(args->length() - orig->arity());
      args->push(TermList(newTrm));

      modified->setTop(true);
      continue;
    }
    toDo->push(tt->next());

    TermList tl=*tt;
    if(tl.isOrdinaryVar()) {
      TermList tDest=applicator.apply(tl.var());
      args->push(tDest);
      if(tDest!=tl) {
        modified->setTop(true);
      }
      continue;
    }
    if(tl.isSpecialVar()) {
      TermList tDest=SpecVarHandler<ProcessSpecVars>::apply(applicator,tl.var());
      args->push(tDest);
      if(tDest!=tl) {
        modified->setTop(true);
      }
      continue;
    }
    ASS(tl.isVSpecialVar() || tl.isTerm());
    if(tl.isVar() || (tl.term()->shared() && tl.term()->ground())) {
      args->push(tl);
      continue;
    }
    Term* t = tl.term();
    if(t->isSpecial()) {
      //we handle specal terms at the top level of this function
      args->push(TermList(applyImpl<ProcessSpecVars>(t, applicator, noSharing)));
      continue;
    }
    terms->push(t);
    modified->push(false);
    toDo->push(t->args());
  }
  ASS(toDo->isEmpty());
  ASS(terms->isEmpty());
  ASS_EQ(modified->length(),1);
  ASS_EQ(args->length(),trm->arity());

  Term* result;
  if(!modified->pop()) {
    result=trm;
  }
  else {
    //here we assume, that stack is an array with
    //second topmost element as &top()-1, third at
    //&top()-2, etc...
    TermList* argLst=&args->top() - (trm->arity()-1);
    ASS_EQ(args->size(), trm->arity());
    if(trm->isLiteral()) {
      ASS(!noSharing);
      Literal* lit = static_cast<Literal*>(trm);
      result=Literal::create(lit,argLst);
    } else if(trm->isSort()){
      ASS(!noSharing);
      result=AtomicSort::create(static_cast<AtomicSort*>(trm),argLst);
    } else {
      bool shouldShare=!noSharing && canBeShared(argLst, trm->arity());
      if(shouldShare) {
        result=Term::create(trm,argLst);          
      } else {
        //At the memoent all sorts should be shared.
        result=Term::createNonShared(trm,argLst);
      }
    }
  }

  Recycler::release(args);
  Recycler::release(modified);
  Recycler::release(terms);
  Recycler::release(toDo);

  return result;
}

/**
 * Apply a substitution to a rectified formula. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var) and, if ProcessSpecVars
 * is set to true, also TermList applyToSpecVar(unsigned specVar).
 *
 * If @b trm can be shared and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 *
 * The specified substitution must be an identity on variables
 * bound inside the formula.
 *
 * This function can handle special terms.
 * This function can handle the substitution of sorts. 
 */
template<bool ProcessSpecVars, class Applicator>
Formula* SubstHelper::applyImpl(Formula* f, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::applyImpl(Formula*...)");

  switch (f->connective()) {
  case LITERAL:
  {
    Literal* lit = static_cast<Literal*>(applyImpl<ProcessSpecVars>(f->literal(), applicator, noSharing));
    return lit == f->literal() ? f : new AtomicFormula(lit);
  }

  case AND:
  case OR:
  {
    FormulaList* newArgs = applyImpl<ProcessSpecVars>(f->args(), applicator, noSharing);
    if (newArgs == f->args()) {
      return f;
    }
    return new JunctionFormula(f->connective(), newArgs);
  }

  case IMP:
  case IFF:
  case XOR:
  {
    Formula* l = applyImpl<ProcessSpecVars>(f->left(), applicator, noSharing);
    Formula* r = applyImpl<ProcessSpecVars>(f->right(), applicator, noSharing);
    if (l == f->left() && r == f->right()) {
      return f;
    }
    return new BinaryFormula(f->connective(), l, r);
  }

  case NOT:
  {
    Formula* arg = applyImpl<ProcessSpecVars>(f->uarg(), applicator, noSharing);
    if (f->uarg() == arg) {
      return f;
    }
    return new NegatedFormula(arg);
  }

  case FORALL:
  case EXISTS:
  {
    bool varsModified = false;
    VList* newVars = VList::empty();
    VList::Iterator vit(f->vars());
    while(vit.hasNext()) {
      unsigned v = vit.next();
      TermList binding = applicator.apply(v);
      ASS(binding.isVar());
      unsigned newVar = binding.var();
      VList::push(newVar, newVars);
      if(newVar!=v) {
        varsModified = true;
      }
    }

    Formula* arg = applyImpl<ProcessSpecVars>(f->qarg(), applicator, noSharing);
    if (!varsModified && arg == f->qarg()) {
      VList::destroy(newVars);
      return f;
    }
    //TODO compute an updated sorts list
    return new QuantifiedFormula(f->connective(),newVars,0,arg);
  }

  case BOOL_TERM:
    return BoolTermFormula::create(applyImpl<ProcessSpecVars>(f->getBooleanTerm(), applicator, noSharing));

  case TRUE:
  case FALSE:
    return f;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Apply a substitution to a rectified list of formulas. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var) and, if ProcessSpecVars
 * is set to true, also TermList applyToSpecVar(unsigned specVar).
 *
 * If @b trm can be shared and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 *
 * The specified substitution must be an identity on variables
 * bound inside the formula.
 *
 * This function can handle special terms.
 */
template<bool ProcessSpecVars, class Applicator>
FormulaList* SubstHelper::applyImpl(FormulaList* fs, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::applyImpl(FormulaList*...)");

  if (FormulaList::isEmpty(fs)) {
    return fs;
  }

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
    Formula* h = applyImpl<ProcessSpecVars>(g, applicator, noSharing);
    FormulaList* hs = res; // = applyImpl<ProcessSpecVars>(gs, applicator, noSharing);

    if (gs == hs && g == h) {
      res = fs;
    } else {
      res = new FormulaList(h,hs);
    }
  }

  return res;
} // SubstHelper::applyImpl

};

#endif /* __SubstHelper__ */
