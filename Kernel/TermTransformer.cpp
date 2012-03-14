/**
 * @file TermTransformer.cpp
 * Implements class TermTransformer.
 */

#include "SortHelper.hpp"
#include "Term.hpp"

#include "TermTransformer.hpp"

namespace Kernel
{

Literal* TermTransformer::transform(Literal* lit)
{
  CALL("TermTransformer::transform(Literal* lit)");
  ASS(lit->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(lit->args());

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
      args.truncate(args.length() - orig->arity());

      args.push(TermList(Term::create(orig,argLst)));
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    TermList dest=transformSubterm(tl);
    if(tl!=dest) {
      args.push(dest);
      modified.setTop(true);
      continue;
    }
    if(tl.isVar()) {
      args.push(tl);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(),1);
  ASS_EQ(args.length(),lit->arity());

  if(!modified.pop()) {
    return lit;
  }

  ASS_EQ(args.size(), lit->arity());
  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (lit->arity()-1);
  return Literal::create(lit,argLst);
}

}
