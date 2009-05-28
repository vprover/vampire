/**
 * @file SubstHelper.hpp
 * Defines class SubstHelper.
 */


#ifndef __SubstHelper__
#define __SubstHelper__

#include "../Lib/DArray.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class SubstHelper
{
public:
  template<class Applicator>
  static TermList apply(TermList t, Applicator& applicator, bool noSharing=false);

  template<class Applicator>
  static Term* apply(Term* t, Applicator& applicator, bool noSharing=false);

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
    TermList apply(unsigned var) { return _map.get(var); }
  private:
    Map* _map;
  };

  template<class Map>
  MapApplicator<Map> getMapApplicator(Map* m)
  {
    return MapApplicator<Map>(m);
  }

};

/**
 * Apply a substitution to a term. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var)
 */
template<class Applicator>
TermList SubstHelper::apply(TermList trm, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::apply(TermList...)");

  if(trm.isOrdinaryVar()) {
    return applicator.apply(trm.var());
  } else {
    ASS(trm.isTerm());
    return TermList(apply(trm.term(), applicator, noSharing));
  }
}


/**
 * Apply a substitution to a term. Substitution is
 * specified by the applicator -- an object with method
 * TermList apply(unsigned var).
 *
 * If @b trm is a shared term and @b noSharing parameter
 * is false, all newly created terms will be inserted into
 * the sharing structure. Otherwise they will not be shared.
 */
template<class Applicator>
Term* SubstHelper::apply(Term* trm, Applicator& applicator, bool noSharing)
{
  CALL("SubstHelper::apply(Term*...)");

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(trm->args());

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      if(terms.isEmpty()) {
	//we're done, args stack contains modified arguments
	//of the literal.
	ASS(toDo.isEmpty());
	break;
      }
      Term* orig=terms.pop();
      if(!modified.pop()) {
	args.truncate(args.length() - orig->arity());
	args.push(TermList(orig));
	continue;
      }
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);

      Term* newTrm;
      if(noSharing || !orig->shared()) {
	newTrm=Term::createNonShared(orig,argLst);
      } else {
	newTrm=Term::create(orig,argLst);
      }
      args.truncate(args.length() - orig->arity());
      args.push(TermList(newTrm));

      modified.setTop(true);
      continue;
    }
    toDo.push(tt->next());

    TermList tl=*tt;
    if(tl.isOrdinaryVar()) {
      TermList tDest=applicator.apply(tl.var());
      args.push(tDest);
      if(tDest!=tl) {
	modified.setTop(true);
      }
      continue;
    }
    if(tl.isSpecialVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    if(t->shared() && t->ground()) {
      args.push(tl);
      continue;
    }
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),trm->arity());

  if(!modified.pop()) {
    return trm;
  }

  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (trm->arity()-1);
  if(trm->isLiteral()) {
    ASS(!noSharing);
    return Literal::create(static_cast<Literal*>(trm),argLst);
  } else {
    if(noSharing || !trm->shared()) {
      return Term::createNonShared(trm,argLst);
    } else {
      return Term::create(trm,argLst);
    }
  }
}

};

#endif /* __SubstHelper__ */
