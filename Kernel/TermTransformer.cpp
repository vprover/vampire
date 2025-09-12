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
 * @file TermTransformer.cpp
 * Implements class TermTransformer.
 */

#include "SortHelper.hpp"
#include "Term.hpp"

#include "TermTransformer.hpp"
#include "FormulaTransformer.hpp"

namespace Kernel
{

using namespace std;


Literal* TermTransformerCommon::transformLiteral(Literal* lit)
{
  Term* t = transform(static_cast<Term*>(lit));
  ASS(t->isLiteral());
  return static_cast<Literal*>(t);
}

Term* TermTransformerCommon::transformSpecial(Term* term)
{
  ASS(term->isSpecial());

  Term::SpecialTermData* sd = term->getSpecialData();
  switch (sd->specialFunctor()) {
    case SpecialFunctor::ITE: {
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

    case SpecialFunctor::FORMULA: {
      Formula* formula = transform(sd->getFormula());

      if (formula == sd->getFormula()) {
        return term;
      } else {
        return Term::createFormula(formula);
      }
    }

    case SpecialFunctor::LET: {
      TermList binding = transform(sd->getBinding());
      TermList body = transform(*term->nthArgument(0));

      if ((binding == sd->getBinding() && (body == *term->nthArgument(0)))) {
        return term;
      } else {
        return Term::createLet(sd->getFunctor(), sd->getVariables(), binding, body, sd->getSort());
      }
    }

    case SpecialFunctor::LET_TUPLE: {
      TermList binding = transform(sd->getBinding());
      TermList body = transform(*term->nthArgument(0));

      if ((binding == sd->getBinding()) && (body == *term->nthArgument(0))) {
        return term;
      } else {
        return Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), binding, body, sd->getSort());
      }
      break;
    }

    case SpecialFunctor::TUPLE: {
      Term* tupleTerm = transform(sd->getTupleTerm());

      if (tupleTerm == sd->getTupleTerm()) {
        return term;
      } else {
        return Term::createTuple(tupleTerm);
      }
    }

    case SpecialFunctor::LAMBDA:
      NOT_IMPLEMENTED;
    case SpecialFunctor::MATCH: {
      DArray<TermList> terms(term->arity());
      bool unchanged = true;
      for (unsigned i = 0; i < term->arity(); i++) {
        terms[i] = transform(*term->nthArgument(i));
        unchanged = unchanged && (terms[i] == *term->nthArgument(i));
      }

      if (unchanged) {
        return term;
      }
      return Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin());
    }

  }
  ASSERTION_VIOLATION_REP(term->toString());
}

/**
 * TODO: functions transform and transformSpecial call each other to process FOOL subterms,
 * a fully non-recursive implementation is pretty complicated and is left for the future
 */
Term* TermTransformer::transform(Term* term)
{
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

  for (;;) {
    TermList* tt = toDo.pop();

    if (tt->isEmpty()) {
      if (terms.isEmpty()) {
        //we're done, args stack contains modified arguments
        //of the literal.
        ASS(toDo.isEmpty());
        break;
      }
      Term* orig = terms.pop();
      ASS(!orig->isSpecial());
      if (!modified.pop()) {
        args.truncate(args.length() - orig->arity());
        args.push(TermList(orig));
        continue;
      }

      //here we assume, that stack is an array with
      //second topmost element as &top()-1, third at
      //&top()-2, etc...
      TermList *argLst = &args.top() - (orig->arity() - 1);
      args.truncate(args.length() - orig->arity()); // potentially evil. Calls destructors on the truncated objects, which we are happily reading just below
      Term* newTrm;
      if(orig->isSort()){
        //For most applications we probably dont want to transform sorts.
        //However, we don't enforce that here, inheriting classes can decide
        //for themselves
        newTrm=AtomicSort::create(static_cast<AtomicSort*>(orig), argLst);
      } else {
        newTrm=Term::create(orig,argLst);
      }
      args.push(TermList(newTrm));
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl = *tt;
    if (tl.isTerm() && tl.term()->isSpecial()) {
      Term* td = transformSpecial(tl.term());
      if (td != tl.term()) {
        modified.setTop(true);
      }
      args.push(TermList(td));
      continue;
    }

    TermList dest = transformSubterm(tl);
    if (tl != dest) {
      args.push(dest);
      modified.setTop(true);
      continue;
    }
    if (tl.isVar()) {
      args.push(tl);
      continue;
    }

    ASS(tl.isTerm());
    Term* t = tl.term();
    ASS(!t->isSpecial());
    terms.push(t);
    modified.push(false);
    toDo.push(t->args());
  }
  ASS(toDo.isEmpty());
  ASS(terms.isEmpty());
  ASS_EQ(modified.length(), 1);
  ASS_EQ(args.length(), term->arity());

  if (!modified.pop()) {
    return term;
  }

  ASS_EQ(args.size(), term->arity());
  //here we assume, that stack is an array with
  //second topmost element as &top()-1, third at
  //&top()-2, etc...
  TermList* argLst = &args.top() - (term->arity() - 1);

  if (term->isLiteral()) {
    return Literal::create(static_cast<Literal*>(term), argLst);
  } else {
    return Term::create(term, argLst);
  }
}

TermList TermTransformer::transform(TermList ts)
{
  // first let's try transforming ts directly
  TermList transformed = transformSubterm(ts);
  if (transformed != ts) {
    // we did transform, so we are done
    return transformed;
  } else if (ts.isVar()) {
    // we didn't transform, but it's a var (no way to recurse)
    return ts;
  } else {
    // try transform subterms
    ASS(ts.isTerm());
    return TermList(transform(ts.term()));
  }
}

Formula* TermTransformer::transform(Formula* f)
{
  TermTransformingFormulaTransformer ttft(*this);
  return ttft.transform(f);
}

Term* BottomUpTermTransformer::transform(Term* term)
{
  if (term->isSpecial()) {
    return transformSpecial(term);
  }

  Stack<TermList*> toDo(8);
  Stack<Term*> terms(8);
  Stack<TermList> args(8);

  toDo.push(term->args());

  // cout << "transform " << term->toString() << endl;

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

        // cout << "args.length() - orig->arity() = " << args.length() - orig->arity() << endl;
        args.truncate(args.length() - orig->arity());
      }

      if(orig->isSort()){
        //For most applications we probably dont want to transform sorts
        //however, we don't enforce that here, inheriting classes can decide
        //for themselves
        args.push(transformSubterm(TermList(AtomicSort::create(static_cast<AtomicSort*>(orig),argLst))));
      } else {
        args.push(transformSubterm(TermList(Term::create(orig,argLst))));
      }
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
    if (tl.isTerm() && tl.term()->isSpecial()) {
      Term* td = transformSpecial(tl.term());
      args.push(TermList(td));
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
#if VDEBUG
  // don't touch args.top() in DEBUG mode if there are actually no arguments (empty stacks don't like it)
  TermList* argLst= args.size() ? &args.top() - (term->arity() - 1) : nullptr;
#else // in release, it's fine too, because Literal::create won't touch the pointer in the zero arity case
  TermList* argLst=               &args.top() - (term->arity() - 1);
#endif
  if (term->isLiteral()) {
    return Literal::create(static_cast<Literal*>(term), argLst);
  } else {
    return Term::create(term, argLst);
  }
}

Formula* BottomUpTermTransformer::transform(Formula* f)
{
  static BottomUpTermTransformerFormulaTransformer ttft(*this);
  return ttft.transform(f);
}

TermList BottomUpTermTransformer::transform(TermList ts)
{
  if (ts.isTerm()) {
    return TermList(transform(ts.term()));
  } else {
    return transformSubterm(ts);
  }
}

}
