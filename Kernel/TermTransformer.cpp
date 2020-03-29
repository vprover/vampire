
/*
 * File TermTransformer.cpp.
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
 * @file TermTransformer.cpp
 * Implements class TermTransformer.
 */

#include "SortHelper.hpp"
#include "Term.hpp"

#include "TermTransformer.hpp"
#include "FormulaTransformer.hpp"

namespace Kernel
{

/**
 * TODO: functions transform and transformSpecial call each other to process FOOL subterms,
 * a fully non-recursive implementation is pretty complicated and is left for the future
 */
Term* TermTransformer::transform(Term* term)
{
  CALL("TermTransformer::transform(Term* term)");

  if (term->isSpecial()) {
    return transformSpecial(term);
  }

  Stack<TermList*> toDo(8);
  Stack<Term*> terms(8);
  Stack<bool> modified(8);
  Stack<TermList> args(8);
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
        if (!orig->isSpecial()) {
          args.truncate(args.length() - orig->arity());
        }
	args.push(TermList(orig));
	continue;
      }

      if (orig->isSpecial()) {
        args.push(TermList(orig));
      } else {
        //here we assume, that stack is an array with
        //second topmost element as &top()-1, third at
        //&top()-2, etc...
        TermList *argLst = &args.top() - (orig->arity() - 1);
        args.truncate(args.length() - orig->arity());
        args.push(TermList(Term::create(orig, argLst)));
      }
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl=*tt;
    TermList dest;
    if (tl.isTerm() && tl.term()->isSpecial()) {
      Term* td = transformSpecial(tl.term());
      if (td == tl.term()) {
        dest = tl;
      } else {
        dest = TermList(td);
      }
    } else {
      dest = transformSubterm(tl);
    }
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
    if (t->isSpecial()) {
      TermList aux[1];
      aux[0].makeEmpty();
      toDo.push(aux);
    } else {
      toDo.push(t->args());
    }
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

Term* TermTransformer::transformSpecial(Term* term)
{
  CALL("TermTransformer::transformSpecial(Term* term)");
  ASS(term->isSpecial());

  Term::SpecialTermData* sd = term->getSpecialData();
  switch (sd->getType()) {
    case Term::SF_ITE: {
      Formula* condition = transform(sd->getCondition());
      TermList thenBranch = transform(*term->nthArgument(0));
      TermList elseBranch = transform(*term->nthArgument(1));

      if ((condition == sd->getCondition()) &&
          (thenBranch == *term->nthArgument(0)) &&
          (elseBranch == *term->nthArgument(1))) {
        return term;
      } else {
        return Term::createITE(condition, thenBranch, elseBranch, sd->getSort());
      }
    }

    case Term::SF_FORMULA: {
      Formula* formula = transform(sd->getFormula());

      if (formula == sd->getFormula()) {
        return term;
      } else {
        return Term::createFormula(formula);
      }
    }

    case Term::SF_LET: {
      TermList binding = transform(sd->getBinding());
      TermList body = transform(*term->nthArgument(0));

      if ((binding == sd->getBinding() && (body == *term->nthArgument(0)))) {
        return term;
      } else {
        return Term::createLet(sd->getFunctor(), sd->getVariables(), binding, body, sd->getSort());
      }
    }

    case Term::SF_LET_TUPLE: {
      TermList binding = transform(sd->getBinding());
      TermList body = transform(*term->nthArgument(0));

      if ((binding == sd->getBinding()) && (body == *term->nthArgument(0))) {
        return term;
      } else {
        return Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), binding, body, sd->getSort());
      }
      break;
    }

    case Term::SF_TUPLE: {
      Term* tupleTerm = transform(sd->getTupleTerm());

      if (tupleTerm == sd->getTupleTerm()) {
        return term;
      } else {
        return Term::createTuple(tupleTerm);
      }
    }

  }
  ASSERTION_VIOLATION_REP(term->toString());
  return nullptr;
}

TermList TermTransformer::transform(TermList ts)
{
  CALL("TermTransformer::transform(TermList ts)");

  if (ts.isVar()) {
    return transformSubterm(ts);
  } else {
    Term* transformed = transform(ts.term());
    if (transformed != ts.term()) {
      return TermList(transformed);
    } else {
      return ts;
    }
  }
}

Formula* TermTransformer::transform(Formula* f)
{
  CALL("TermTransformer::transform(Formula* f)");
  TermTransformingFormulaTransformer ttft(*this);
  return ttft.transform(f);
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

Formula* TermTransformerTransformTransformed::transform(Formula* f)
{
  CALL("TermTransformerTransformTransformed::transform(Formula* f)");
  static TermTransformerTransformTransformedFormulaTransformer ttft(*this);
  return ttft.transform(f);
}

}
