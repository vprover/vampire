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
#include "ApplicativeHelper.hpp"

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

  onTermEntry(term);

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
        
      onTermExit(orig);

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
      Term* newTrm = orig->isSort() ? 
        create<AtomicSort> (orig, argLst, _sharedResult) :
        create<Term>       (orig, argLst, _sharedResult) ;
      args.push(TermList(newTrm));
      modified.setTop(true);
      continue;
    } else {
      toDo.push(tt->next());
    }

    TermList tl = *tt;

    // We still transform sort and term variables ...
    // It is difficult to avoid this though
    if(tl.isTerm() && tl.term()->isSort() && _dontTransformSorts){
      args.push(tl);
      continue;      
    }

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
      modified.setTop(true);
    }
    if (dest.isVar() || !exploreSubterms(tl, dest)) {
      args.push(dest);
      continue;
    }

    ASS(dest.isTerm());
    Term* t = dest.term();
    
    onTermEntry(t);

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

  if(term->isLiteral()){
    Literal* lit = static_cast<Literal*>(term);
    if(lit->isEquality() && argLst[0].isVar() && argLst[1].isVar() && !_dontTransformSorts){
      return Literal::createEquality(lit->polarity(), argLst[0], argLst[1], 
        transform(SortHelper::getEqualityArgumentSort(lit)));
    }
    return create<Literal> (term, argLst, _sharedResult);
  } else if (term->isSort()){
    return create<AtomicSort>(term, argLst, _sharedResult);
  }
  return create<Term>(term, argLst, _sharedResult);
}

// default implementation, can override if required
bool TermTransformer::exploreSubterms(TermList orig, TermList newTerm)
{
  CALL("TermTransformer::exploreSubterms");
  ASS(newTerm.isTerm())

  if(orig != newTerm) return false;
  return true;
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

    case Term::SF_MATCH: {
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

TermList SubtermReplacer::transformSubterm(TermList t)
{
  CALL("SubtermReplacer::transformSubterm");

  if(t == _what){ 
#if VHOL
    if(_liftFreeIndices)
    { return TermShifter().shift(_by, _shiftBy); }
#endif
    return _by;
  }
  return t;
}

#if VHOL

void SubtermReplacer::onTermEntry(Term* t)
{
  CALL("SubtermReplacer::onTermEntry");

  if(t->isLambdaTerm()) _shiftBy++;
}

void SubtermReplacer::onTermExit(Term* t)
{
  CALL("SubtermReplacer::onTermExit");

  if(t->isLambdaTerm()) _shiftBy--;
}

#endif

TypedTermList ToBank::toBank(TypedTermList term){
  CALL("ToBank::toBank");

  TermList sort = term.sort();
  
  if(term.isTerm()){
    return TypedTermList(transform(term).term());
  } else {
    return TypedTermList(transformSubterm(term), 
      sort.isVar() ? transformSubterm(sort) : transform(sort));
  }
}

TermList ToBank::transformSubterm(TermList t) {
  CALL("ToBank::transformSubterm");

  if(t.isVar() && t.bank() != _bank){
    return TermList(t.var(), _bank);
  }
  return t;
}

bool ToBank::exploreSubterms(TermList orig, TermList newTerm) {
  CALL("ToBank::exploreSubterms");

  return !(newTerm.isTerm() && newTerm.term()->shared() && newTerm.term()->ground()); 
}

Formula* TermTransformer::transform(Formula* f)
{
  CALL("TermTransformer::transform(Formula* f)");
  TermTransformingFormulaTransformer ttft(*this);
  return ttft.transform(f);
}

Term* BottomUpTermTransformer::transform(Term* term)
{
  CALL("BottomUpTermTransformer::transform(Term* term)");
  ASS(term->shared());

  static Stack<TermList*> toDo(8);
  static Stack<Term*> terms(8);
  static Stack<TermList> args(8);
  /* all stacks must be reset since the function might have been aborted by an exception */
  args.reset();
  terms.reset();
  toDo.reset(); 

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

Literal* BottomUpTermTransformer::transform(Literal* lit)
{
  CALL("TermTransformer::transform(Literal* lit)");
  Term* t = transform(static_cast<Term*>(lit));
  ASS(t->isLiteral());
  return static_cast<Literal*>(t);
}

Formula* BottomUpTermTransformer::transform(Formula* f)
{
  CALL("BottomUpTermTransformer::transform(Formula* f)");
  static BottomUpTermTransformerFormulaTransformer ttft(*this);
  return ttft.transform(f);
}

}
