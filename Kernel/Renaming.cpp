/**
 * @file Renaming.cpp
 * Implements class Renaming
 */

#include "../Lib/DArray.hpp"
#include "../Indexing/TermSharing.hpp"
#include "Renaming.hpp"

#if VDEBUG
#include "../Lib/Int.hpp"
#include "../Lib/Set.hpp"
#endif

using namespace Lib;
using namespace Indexing;
using namespace Kernel;

Literal* Renaming::apply(Literal* lit) const
{
  CALL("Renaming::apply(Literal*...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    ts[i++]=apply(*args);
  }
  return Literal::create(lit,ts.array());
}

Term* Renaming::apply(Term* trm) const
{
  CALL("Renaming::apply(Term*...)");

  if(trm->isLiteral()) {
    return apply(static_cast<Literal*>(trm));
  }

  TermList res=apply(TermList(trm));
  ASS(res.isTerm());
  return res.term();
}

TermList Renaming::apply(TermList trm) const
{
  CALL("Renaming::apply(TermList...)");
  ASS(!trm.isTerm() || trm.term()->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<TermList> args(8);

  toDo.push(&trm);

  while(!toDo.isEmpty()) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      Term* orig=terms.pop();
      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList* argLst=&args.top() - (orig->arity()-1);
      args.truncate(args.length() - orig->arity());
      TermList constructed;
      constructed.setTerm(Term::create(orig,argLst));
      args.push(constructed);
      continue;
    } else {
      //if tt==&trm, we're dealing with the top
      //term, for which the next() is undefined
      if(tt!=&trm) {
	toDo.push(tt->next());
      }
    }

    TermList tl=*tt;

    if(tl.isVar()) {
      if(tl.isOrdinaryVar()) {
	tl.makeVar(apply(tt->var()));
      }
      args.push(tl);
      continue;
    }
    Term* t=tl.term();
    if(t->ground()) {
      args.push(tl);
      continue;
    }
    terms.push(t);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty() && terms.isEmpty() && args.length()==1);
  return args.pop();
}

bool Renaming::identity() const
{
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    if(from!=to) {
      return false;
    }
  }
  return true;
}


void Renaming::normalizeVariables(const Term* t, Renaming& res)
{
  Term::VariableIterator vit(t);
  while(vit.hasNext()) {
    TermList var=vit.next();
    if(var.isOrdinaryVar()) {
      res.getOrBind(var.var());
    }
  }
}

void Renaming::normalizeVariables(TermList t, Renaming& res)
{
  if(t.isOrdinaryVar()) {
    res.getOrBind(t.var());
  } else if(t.isTerm()) {
    normalizeVariables(t.term(),res);
  }
}

void Renaming::inverse(const Renaming& orig, Renaming& target)
{
  VariableMap::Iterator mit(orig._data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    ALWAYS(target._data.set(to,from));
  }
}

#if VDEBUG

void Renaming::assertValid() const
{
  Set<unsigned> range;
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned to = mit.next();
    ASS(!range.contains(to));
    range.insert(to);
  }
}

std::string Renaming::toString() const
{
  std::string res;
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    res+=Int::toString(from)+" -> "+Int::toString(to)+"\n";
  }
  return res;
}

#endif
