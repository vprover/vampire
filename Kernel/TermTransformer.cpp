/**
 * @file TermTransformer.cpp
 * Implements class TermTransformer.
 */

#include "SortHelper.hpp"
#include "Term.hpp"

#include "TermTransformer.hpp"

namespace Kernel
{

Term* TermTransformer::transform(Term* term)
{
  CALL("TermTransformer::transform(Term* term)");
  ASS(term->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<bool> modified(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  modified.reset();
  args.reset();

  modified.push(false);
  toDo.push(term->args());

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
  ASS_EQ(args.length(), term->arity());

  if(!modified.pop()) {
    return term;
  }

  ASS_EQ(args.size(), term->arity());
  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (term->arity() - 1);

  if (term->isLiteral()) {
    return Literal::create(static_cast<Literal*>(term), argLst);
  } else {
    return Term::create(term, argLst);
  }
}

Literal* TermTransformer::transform(Literal* lit)
{
  CALL("TermTransformer::transform(Literal* lit)");
  Term* t = transform(static_cast<Term*>(lit));
  ASS(t->isLiteral());
  return static_cast<Literal*>(t);
}

Term* TermTransformerTransformTransformed::transform(Term* term)
{
  CALL("TermTransformerTransformTransformed::transform(Term* term)");
  ASS(term->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<TermList> args(8);
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  args.reset();

  toDo.push(term->args());

  // cout << "transform " << lit->toString() << endl;

  for(;;) {
    TermList* tt=toDo.pop();
    if(tt->isEmpty()) {
      // cout << "empty "  << endl;

      if(terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig=terms.pop();

      // cout << "term popped " << orig->toString() << endl;

      TermList* argLst = 0;
      if (orig->arity()) {
        //here we assume, that stack is an array with
        //second topmost element as &top()-1, third at
        //&top()-2, etc...
        argLst=&args.top() - (orig->arity()-1);
        args.truncate(args.length() - orig->arity());
      }

      // cout << "args.length() - orig->arity() = " << args.length() - orig->arity() << endl;

      args.push(transformSubterm(TermList(Term::create(orig,argLst))));
      continue;
    } else {
      toDo.push(tt->next());
    }

    // cout << "Non-empty: " <<  tt->toString() << endl;

    TermList tl=*tt;
    if(tl.isVar()) {
      TermList dest=transformSubterm(tl);
      args.push(dest);
      continue;
    }
    ASS(tl.isTerm());
    Term* t=tl.term();
    terms.push(t);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(args.length(), term->arity());

  ASS_EQ(args.size(), term->arity());
  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst=&args.top() - (term->arity() - 1);
  if (term->isLiteral()) {
    return Literal::create(static_cast<Literal*>(term), argLst);
  } else {
    return Term::create(term, argLst);
  }
}

Literal* TermTransformerTransformTransformed::transform(Literal* lit)
{
  CALL("TermTransformer::transform(Literal* lit)");
  Term* t = transform(static_cast<Term*>(lit));
  ASS(t->isLiteral());
  return static_cast<Literal*>(t);
}

}
