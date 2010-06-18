/**
 * @file SubstHelper.hpp
 * Defines class SubstHelper.
 */


#ifndef __SubstHelper__
#define __SubstHelper__

#include "Lib/DArray.hpp"
#include "Lib/Recycler.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class SubstHelper
{
public:
  template<class Applicator>
  static TermList apply(TermList t, Applicator& applicator, bool noSharing=false)
  {
    return applyImpl<false,Applicator>(t, applicator, noSharing);
  }

  template<class Applicator>
  static Term* apply(Term* t, Applicator& applicator, bool noSharing=false)
  {
    return applyImpl<false,Applicator>(t, applicator, noSharing);
  }

  /**
   * Apply a substitution to a literal. Substitution is
   * specified by the applicator -- an object with method
   * TermList apply(unsigned var)
   */
  template<class Applicator>
  static Literal* apply(Literal* lit, Applicator& applicator)
  {
    return static_cast<Literal*>(apply(static_cast<Term*>(lit),applicator));
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
    TermList apply(unsigned var) { return _map->get(var); }
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
 * TermList apply(unsigned var)
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
 * If @b trm is a shared term and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 */
template<bool ProcessSpecVars, class Applicator>
Term* SubstHelper::applyImpl(Term* trm, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::applyImpl(Term*...)");

  using namespace SubstHelper_Aux;

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
	//of the literal.
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

      Term* newTrm;
      if(noSharing || !orig->shared()) {
	newTrm=Term::createNonShared(orig,argLst);
      } else {
	newTrm=Term::create(orig,argLst);
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
    ASS(tl.isTerm());
    Term* t=tl.term();
    if(t->shared() && t->ground()) {
      args->push(tl);
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
    if(trm->isLiteral()) {
      ASS(!noSharing);
      result=Literal::create(static_cast<Literal*>(trm),argLst);
    } else {
      bool shouldShare=!noSharing && trm->shared();
      if(!noSharing && !trm->shared()) {
	shouldShare=true;
	for(unsigned i=0;i<trm->arity();i++) {
	  if(argLst[i].isSpecialVar()||(argLst[i].isTerm()&&!argLst[i].term()->shared())) {
	    shouldShare=false;
	    break;
	  }
	}
      }
      if(!shouldShare) {
	result=Term::createNonShared(trm,argLst);
      } else {
	result=Term::create(trm,argLst);
      }
    }
  }

  Recycler::release(args);
  Recycler::release(modified);
  Recycler::release(terms);
  Recycler::release(toDo);

  return result;
}

};

#endif /* __SubstHelper__ */
