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
 * @file SymCounter.cpp
 * Implements class SymCounter counting occurrences of function
 * and predicate symbols.
 *
 * @since 01/05/2002, Manchester
 */

#include <Kernel/TermIterators.hpp>
#include "Lib/Allocator.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Unit.hpp"

#include "SymCounter.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Initialise SymCounter.
 * @since 09/06/2007 Manchester
 */
SymCounter::SymCounter (Signature& sig)
  :
  _noOfPreds(sig.predicates()),
  _noOfFuns (sig.functions()),
  _noOfTypeCons(sig.typeCons())
{
  CALL("SymCounter::SymCounter");

  if (_noOfPreds) {
    void* mem = ALLOC_KNOWN(_noOfPreds*sizeof(Pred),"SymCounter::Pred[]");
    _preds = array_new<Pred>(mem, _noOfPreds);
  }

  if (_noOfFuns) {
    void* mem = ALLOC_KNOWN(_noOfFuns*sizeof(FunOrTypeCon),"SymCounter::Fun[]");
    _funs = array_new<FunOrTypeCon>(mem, _noOfFuns);
  }

  if (_noOfTypeCons) {
    void* mem = ALLOC_KNOWN(_noOfTypeCons*sizeof(FunOrTypeCon),"SymCounter::TypeCon[]");
    _typeCons = array_new<FunOrTypeCon>(mem, _noOfTypeCons);
  }  
} // SymCounter::SymCounter


/**
 * Destroy a symbol counter
 * @since 01/05/2002, Manchester
 */
SymCounter::~SymCounter ()
{
  CALL("SymCounter::~SymCounter");

  if (_noOfPreds) {
    array_delete(_preds,_noOfPreds);
    DEALLOC_KNOWN(_preds,_noOfPreds*sizeof(Pred),"SymCounter::Pred[]");
  }
  if (_noOfFuns) {
    array_delete(_funs,_noOfFuns);
    DEALLOC_KNOWN(_funs,_noOfFuns*sizeof(FunOrTypeCon),"SymCounter::Fun[]");
  }
  if (_noOfTypeCons) {
    array_delete(_typeCons,_noOfTypeCons);
    DEALLOC_KNOWN(_typeCons,_noOfTypeCons*sizeof(FunOrTypeCon),"SymCounter::TypeCon[]");
  }
} // SymCounter::~SymCounter


/**
 * Count symbols in a problem.
 * c must be 1 or -1, 1 means add number of occurrences for each symbol, -1 means subtract
 * @since 01/05/2002, Manchester
 */
void SymCounter::count (UnitList* units,int c)
{
  CALL("SymCounter::count (const UnitList*)");

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    Unit* unit = us.next();
    if (unit->isClause()) {
      count(static_cast<Clause*>(unit),c);
    }
    else {
      count (static_cast<FormulaUnit*>(unit)->formula(),true,c);
    }
  }
} // SymCounter::count (UnitList*,int c)

/**
 * Count symbols in a clause.
 * @since 01/05/2002, Manchester
 * @since 11/09/2002 Manchester, changed
 */
void SymCounter::count (Clause* clause,int add)
{
  CALL("SymCounter::count(const Clause*)");

  for (int n = clause->length()-1;n >= 0;n--) {
    count((*clause)[n],true,add);
  }
} // SymCounter::count (Clause* u,int c)

void SymCounter::count(Formula* f, int add)
{
  count(f, 1, add);
}

/**
 * Count symbols in a formula.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count (Formula* f,int polarity,int add)
{
  CALL("SymCounter::count(const Formula*)");

  switch (f->connective()) {
    case LITERAL:
      count (f->literal(), polarity, add);
      return;

    case AND:
    case OR: {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
        count (fs.next(),polarity,add);
      }
      return;
    }

    case IMP:
      count (f->left(), -polarity, add);
      count (f->right(), polarity, add);
      return;

    case NOT:
      count (f->uarg(), -polarity, add);
      return;

    case IFF:
    case XOR:
      count (f->left(), 0, add);
      count (f->right(), 0, add);
      return;

    case FORALL:
    case EXISTS:
      count (f->qarg(), polarity, add);
      return;

    case BOOL_TERM: {
      TermList ts = f->getBooleanTerm();
      if (!ts.isTerm()) return;
      count (ts.term(), polarity, add);
      return;
    }

  case TRUE:
  case FALSE:
    return;

  case NAME:
  case NOCONN:
      ASSERTION_VIOLATION;
  }
} // SymCounter::count (Formula* f,...)


/**
 * Count symbols in a literal.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count(Literal* l,int polarity,int add)
{
  CALL("SymCounter::count(const Literal*)");

  int pred = l->functor();
  ASS(_noOfPreds > pred);

  _preds[pred].add(l->isPositive() ? polarity : -polarity,add);

  if (!l->shared()) {
    for(TermList* arg=l->args(); arg->isNonEmpty(); arg=arg->next()) {
      if(arg->isTerm()){
        count(arg->term(), 1, add);
      }
    }
    if(l->isTwoVarEquality()){
      TermList sort = l->twoVarEqSort();
      if(sort.isTerm()){
        count(sort.term(), 1, add);
      }
    }
  } else {
    NonVariableIterator nvi(l);
    while (nvi.hasNext()) {
      Term *t = nvi.next().term();
      int fun = t->functor();
      if(!t->isSort()){
        ASS_REP(_noOfFuns > fun, t->toString());
        _funs[fun].add(add);
      } else {
        ASS_REP(_noOfTypeCons > fun, t->toString());
        _typeCons[fun].add(add);        
      }
    }
  }
} // SymCounter::count (Literal* l ...)

/**
 * Count symbols in a term.
 * @since 01/05/2002, Manchester
 */
void SymCounter::count(Term* term, int polarity, int add)
{
  CALL("SymCounter::count(Term*)");

  if (!term->shared()) {
    if (term->isSpecial()) {
      Term::SpecialTermData *sd = term->getSpecialData();
      switch (sd->getType()) {
        case Term::SF_FORMULA:
          count(sd->getFormula(), polarity, add);
              break;
        case Term::SF_ITE:
          count(sd->getCondition(), 0, add);
              break;
        case Term::SF_LET:
        case Term::SF_LET_TUPLE: {
          TermList binding = sd->getBinding();
          if (binding.isTerm()) {
            count(binding.term(), 1, add);
          }
          break;
        }
        case Term::SF_TUPLE: {
          count(sd->getTupleTerm(), 0, add);
          break;
        }
        case Term::SF_LAMBDA: {
          TermList lambdaExp = sd->getLambdaExp();
          if(lambdaExp.isTerm()){
            count(lambdaExp.term(), polarity, add);
          }
          break;
        }
        case Term::SF_MATCH: {
          for (unsigned i = 0; i < term->arity(); i++) {
            TermList t = *term->nthArgument(i);
            if (t.isTerm()) {
              count(t.term(), polarity, add);
            }
          }
          break;
        }
        default:
          ASSERTION_VIOLATION;
      }
    } else {
      //There should never be a non-shared sort
      int fun = term->functor();
      ASS(!term->isSort());
      ASS_REP(_noOfFuns > fun, term->toString());
      _funs[fun].add(add);

      for(TermList* arg=term->args(); arg->isNonEmpty(); arg=arg->next()) {
        if(arg->isTerm()){
          count(arg->term(), 1, add);
        }
      }
    }
  } else {
    int fun = term->functor();
    if(!term->isSort()){
      ASS_REP(_noOfFuns > fun, term->toString());
      _funs[fun].add(add);
    } else {
      ASS_REP(_noOfTypeCons > fun, term->toString());
      _typeCons[fun].add(add);       
    }

    NonVariableIterator nvi(term);
    while (nvi.hasNext()) {
      Term *t = nvi.next().term();
      int fun = t->functor();
      if(!t->isSort()){      
        ASS_REP(_noOfFuns > fun, t->toString());
        _funs[fun].add(add);
      } else {
        ASS_REP(_noOfTypeCons > fun, t->toString());
        _typeCons[fun].add(add);        
      }
    }
  }
} // SymCounter::count(const Term* f, ...)


/**
 * Count occurrences for a symbol.
 * @since 01/05/2002, Manchester
 */
void SymCounter::Pred::add(int polarity, int add)
{
  CALL("SymCounter::add");

  switch (polarity) {
    case -1:
      _nocc += add;
      return;

    case 0:
      _docc += add;
      return;

    case 1:
      _pocc += add;
      return;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
      return;
#endif
  }
} // SymCounter::Pred::add


