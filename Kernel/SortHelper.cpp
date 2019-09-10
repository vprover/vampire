
/*
 * File SortHelper.cpp.
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
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"

#include "Clause.hpp"
#include "FormulaUnit.hpp"
#include "Signature.hpp"
#include "Sorts.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Substitution.hpp"
#include "SubstHelper.hpp"

#include "SortHelper.hpp"

using namespace Kernel;


/**
 * Return the type of a term or a literal @c t
 * @author Andrei Voronkov
 */
OperatorType* SortHelper::getType(Term* t)
{
  CALL("SortHelper::getType(Term*)");

  if (t->isLiteral()) {
    return env.signature->getPredicate(t->functor())->predType();
  }
  return env.signature->getFunction(t->functor())->fnType();
} // getType

/**
 * Return the type of a term or a literal @c t
 * @author Ahmed Bhayat
 */
void SortHelper::getTypeSub(const Term* t, Substitution& subst)
{
  CALL("SortHelper::getTypeSub(Term*)");
  
  //cout << "attempting to get type Substitution for term " + t->toString() << endl;

  TermList* typeArg;
  OperatorType* ot       = getType(const_cast<Term*>(t)); //sym->fnType();
  //cout << "the type is " + ot->toString() << endl;
  List<unsigned>* vars   = ot->quantifiedVars();
  unsigned typeArgsArity = ot->typeArgsArity();

  typeArg = const_cast<TermList*>(t->args());
  for(unsigned i = 0; i < typeArgsArity; i++){
    unsigned var = vars->head();
    vars = vars->tail();
    //cout << "binding X" << var << " to " << typeArg->toString() << endl; 
    subst.bind(var, *typeArg);
    typeArg = typeArg->next();
  }  
} // getTypeSub

/**
 * Return the sort of a non-variable term t. This function cannot be applied
 * to a special term, such as if-then-else.
 */
TermList SortHelper::getResultSort(const Term* t)
{
  CALL("SortHelper::getResultSort(Term*)");
  ASS(!t->isSpecial());
  ASS(!t->isLiteral());

 // cout << "the term is " + t->toString() + " with functor " << t->functor() << endl;

  Substitution subst;
  getTypeSub(t, subst);
  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  TermList result = sym->fnType()->result();
  //cout << "the type is " + sym->fnType()->toString() << endl;
  ASS(!subst.isEmpty() || (result.isTerm() && result.term()->ground()));  
  return SubstHelper::apply(result, subst);
}

/**
 * Try get result sort of a term.
 *
 * This function can be applied also to special terms such as if-then-else.
 */
bool SortHelper::tryGetResultSort(const Term* t, TermList& result)
{
  CALL("tryGetResultSort(Term*,unsigned&)");
  ASS(!t->isLiteral());

  TermList masterVar;
  return getResultSortOrMasterVariable(t, result, masterVar);
}

bool SortHelper::tryGetResultSort(const TermList t, TermList& result)
{
  CALL("tryGetResultSort(TermList,unsigned&)");
  if (t.isVar()) {
    return false;
  }
  return tryGetResultSort(t.term(), result);
}

/**
 * This function works also for special terms
 */
TermList SortHelper::getResultSort(TermList t, DHMap<unsigned,TermList>& varSorts)
{
  CALL("SortHelper::getResultSort");

  TermList res;
  TermList masterVar;
  if (!getResultSortOrMasterVariable(t, res, masterVar)) {
    ASS(masterVar.isOrdinaryVar());
    res = varSorts.get(masterVar.var());
  }
  return res;
}

/**
 * If sort of term @c t depends on a variable, assign the variable into
 * @c resultVar and return false. Otherwise assign the sort of the term
 * into @c resultSort and return true.
 */
bool SortHelper::getResultSortOrMasterVariable(const Term* t, TermList& resultSort, TermList& resultVar)
{
  CALL("SortHelper::getResultSortOrMasterVariable");

  switch(t->functor()) {
    /*case Term::SF_LET:
    case Term::SF_LET_TUPLE:
    case Term::SF_ITE:
      resultSort = t->getSpecialData()->getSort();
      return true;*/
    case Term::SF_FORMULA:
      resultSort = Term::boolSort();
      return true;
    case Term::SF_LAMBDA: {
      resultSort = t->getSpecialData()->getSort();
      return true;
    }
    /*case Term::SF_TUPLE: {
      resultSort = getResultSort(t->getSpecialData()->getTupleTerm());
      return true;
    }*/
    default:
      ASS(!t->isSpecial());
      resultSort = getResultSort(t);
      return true;
  } //TODO reintroduce specials. For now removing all FOOL work
} // SortHelper::getResultSortOrMasterVariable

/**
 * If sort of term @c t depends on a variable, assign the variable into
 * @c resultVar and return false. Otherwise assign the sort of the term
 * into @c resultSort and return true.
 */
bool SortHelper::getResultSortOrMasterVariable(const TermList t, TermList& resultSort, TermList& resultVar)
{
  CALL("SortHelper::getResultSortOrMasterVariable");

  if (t.isVar()) {
    resultVar = t;
    return false;
  }
  return getResultSortOrMasterVariable(t.term(), resultSort, resultVar);
}

/**
 * Return sort of the argument @c argIndex of the term or literal @c t
 */
TermList SortHelper::getArgSort(Term* t, unsigned argIndex)
{
  CALL("SortHelper::getArgSort(Term*,unsigned)");
  ASS_L(argIndex, t->arity());

  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    return getEqualityArgumentSort(static_cast<Literal*>(t));
  }

  Substitution subst;
  OperatorType* ot = getType(t);

  if(argIndex < ot->typeArgsArity()){
    return Term::superSort();
  }
  
  getTypeSub(t, subst);
  return SubstHelper::apply(ot->arg(argIndex), subst);
} // getArgSort

TermList SortHelper::getEqualityArgumentSort(const Literal* lit)
{
  CALL("SortHelper::getEqualityArgumentSort");
  ASS(lit->isEquality());

  if (lit->isTwoVarEquality()) {
    return lit->twoVarEqSort();
  }

  TermList arg1 = *lit->nthArgument(0);
  TermList srt1;
  if (tryGetResultSort(arg1, srt1)) {
    return srt1;
  }

  TermList arg2 = *lit->nthArgument(1);
  TermList srt2;
  ALWAYS(tryGetResultSort(arg2, srt2));
  return srt2;
} //

/**
 * Return sort of term @c trm that appears inside literal @c lit.
 */
TermList SortHelper::getTermSort(TermList trm, Literal* lit)
{
  CALL("SortHelper::getTermSort");

  if (trm.isTerm()) {
    return getResultSort(trm.term());
  }
  if(!trm.isVar()){
    cout << "ERROR with " << trm.toString() << " in " << lit->toString() << endl;
  }
  ASS(trm.isVar());
  return getVariableSort(trm, lit);
}

/**
 * Return sort of variable @c var in term or literal @c t
 *
 * Variable @c var must occurr in @c t.
 */
TermList SortHelper::getVariableSort(TermList var, Term* t)
{
  CALL("SortHelper::getVariableSort(TermList,Term*)");

  TermList res;
  ALWAYS(tryGetVariableSort(var, t, res));
  return res;
}

/**
 * Return sort of variable @c var in formula @c f.
 *
 * The variable
 */
bool SortHelper::tryGetVariableSort(unsigned var, Formula* f, TermList& res)
{
  CALL("SortHelper::tryGetVariableSort(unsigned,Formula*,unsigned&)");

  TermList varTerm(var, false);

  SubformulaIterator sfit(f);
  while (sfit.hasNext()) {
    Formula* sf = sfit.next();
    if (sf->connective() == LITERAL){

      Literal* lit = sf->literal();

      // first handle the special equality case
      if(lit->isEquality()){
         TermList* left = lit->nthArgument(0);
         TermList* right = lit->nthArgument(1);
         if((left->isVar() && left->var()==var) ||
            (right->isVar() && right->var()==var)){

           res = getEqualityArgumentSort(lit); 
           return true;
         }
      }
      if(tryGetVariableSort(varTerm, lit, res)){
        return true;
      }
    }
    if(sf->connective() == BOOL_TERM){
      TermList stt = sf->getBooleanTerm();
      if(stt.isVar() && stt.var()==var){
        res = Term::boolSort();
        return true;
      }
      if(stt.isTerm()){
        Term* st = stt.term();
        if(tryGetVariableSort(varTerm,st,res)){
          return true;
        } 
      }
    } 
  }
  return false;
}


/**
 * An iterative version to replace the original recursive functions below.
 *
 * @since 13/02/2017 Vienna
 * @author Martin Suda
 */
void SortHelper::collectVariableSortsIter(CollectTask task, DHMap<unsigned,TermList>& map)
{
  CALL("SortHelper::collectVariableSortsIter");

  Stack<CollectTask> todo;

  todo.push(task);
  while (todo.isNonEmpty()) {
    CollectTask task = todo.pop();

    switch(task.fncTag) {
      case COLLECT_TERM: {
        Term* term = task.t;
    
        unsigned position = 0;
        for (TermList* ts = term->args(); ts->isNonEmpty(); ts = ts->next()) {
          CollectTask newTask;
          newTask.fncTag = COLLECT_TERMLIST;
          newTask.ts = *ts;
          newTask.contextSort = getArgSort(term, position++);
          todo.push(newTask);
        }

      } break;

      case COLLECT_TERMLIST: {
        TermList ts = task.ts;

        if (ts.isTerm()) {
          Term* term = ts.term();

          CollectTask newTask;
          newTask.t = term;
          newTask.contextSort = task.contextSort;

          if (term->isSpecial()) {
            newTask.fncTag = COLLECT_SPECIALTERM;
            todo.push(newTask);
          } else {
            newTask.fncTag = COLLECT_TERM;
            todo.push(newTask);
          }
        } else if (ts.isOrdinaryVar()) {
          unsigned var = ts.var();
          if (!map.insert(var, task.contextSort)) {
            ASS_EQ(task.contextSort, map.get(var));
          }
        }

      } break;

      case COLLECT_SPECIALTERM: {
        Term* term = task.t;

        ASS(term->isSpecial());

        Term::SpecialTermData* sd = term->getSpecialData();

        switch (term->functor()) {
          /*case Term::SF_ITE: {
            CollectTask newTask;

            newTask.fncTag = COLLECT_TERMLIST;
            newTask.contextSort = task.contextSort;

            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.ts = *term->nthArgument(1);
            todo.push(newTask);

            newTask.fncTag = COLLECT_FORMULA;
            newTask.f = sd->getCondition();
            todo.push(newTask);

            break;
          }

          case Term::SF_LET: {
            TermList binding = sd->getBinding();
            bool isPredicate = binding.isTerm() && binding.term()->isBoolean();
            Signature::Symbol* symbol = isPredicate ? env.signature->getPredicate(sd->getFunctor())
                                                    : env.signature->getFunction(sd->getFunctor());
            unsigned position = 0;
            Formula::VarList::Iterator vit(sd->getVariables());
            while (vit.hasNext()) {
              unsigned var = (unsigned)vit.next();
              unsigned sort = isPredicate ? symbol->predType()->arg(position) : symbol->fnType()->arg(position);
              if (!map.insert(var, sort)) {
                ASS_EQ(sort, map.get(var));
              }
              position++;
            }

            CollectTask newTask;

            newTask.fncTag = COLLECT_TERMLIST;
            newTask.contextSort = task.contextSort;

            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.ts = binding;
            if (!isPredicate) {
              newTask.contextSort = symbol->fnType()->result();
            }
            todo.push(newTask);

            break;
          }

          case Term::SF_LET_TUPLE: {
            TermList binding = sd->getBinding();
            Signature::Symbol* symbol = env.signature->getFunction(sd->getFunctor());

            CollectTask newTask;
            newTask.fncTag = COLLECT_TERMLIST;
            newTask.contextSort = task.contextSort;
            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.contextSort = symbol->fnType()->result();
            newTask.ts = binding;
            todo.push(newTask);

            break;
          }*/

          case Term::SF_FORMULA: {
            CollectTask newTask;
            newTask.fncTag = COLLECT_FORMULA;
            newTask.f = sd->getFormula();
            todo.push(newTask);
          } break;
          case Term::SF_LAMBDA: {
            CollectTask newTask;
            newTask.fncTag = COLLECT_TERMLIST;
            newTask.contextSort = sd->getLambdaExpSort();
            newTask.ts = sd->getLambdaExp();
            todo.push(newTask);              
          } break;

          /*case Term::SF_TUPLE: {
            CollectTask newTask;
            newTask.fncTag = COLLECT_TERM;
            newTask.t = sd->getTupleTerm();
            todo.push(newTask);
          } break;*/

      #if VDEBUG
          default:
            ASSERTION_VIOLATION;
      #endif
        }
      } break;

      case COLLECT_FORMULA: {
        Formula* f = task.f;

        SubformulaIterator sfit(f);
        while (sfit.hasNext()) {
          Formula* sf = sfit.next();
          switch (sf->connective()) {
            case LITERAL: {
              Literal* lit = sf->literal();
              if(lit->isTwoVarEquality()){
                CollectTask newTask;
                newTask.fncTag = COLLECT_TERMLIST;
                newTask.ts = lit->twoVarEqSort();
                newTask.contextSort = Term::superSort();
                todo.push(newTask);
              }
              CollectTask newTask;
              newTask.fncTag = COLLECT_TERM;
              newTask.t = lit;

              todo.push(newTask);
            } break;

            case BOOL_TERM: {
              TermList ts = sf->getBooleanTerm();
              if (ts.isVar()) {
                if (!map.insert(ts.var(), Term::boolSort())) {
                  ASS_EQ(Term::boolSort(), map.get(ts.var()));
                }
              } else {
                ASS(ts.isTerm());

                CollectTask newTask;
                if(ts.term()->isSpecial()){
                  newTask.fncTag = COLLECT_SPECIALTERM;
                } else {
                  newTask.fncTag = COLLECT_TERM;                  
                }
                newTask.t = ts.term();
                newTask.contextSort = Term::boolSort();

                todo.push(newTask);
              }
              break;
            }

            default:
              continue;
          }
        }

      } break;
    }
  }
}

/**
 * Insert variable sorts from non-shared subterms of @c t0 into @c map. If a
 * variable is in map already (or appears multiple times), assert that the sorts
 * are equal. @c t0 can be either term or literal.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @since 15/05/2015 Gothenburg, FOOL support added
 * @author Andrei Voronkov, Evgeny Kotelnikov
 */
void SortHelper::collectVariableSorts(Term* term, DHMap<unsigned,TermList>& map)
{
  CALL("SortHelper::collectVariableSorts(Term*,...)");

  CollectTask t;
  t.fncTag = COLLECT_TERM;
  t.t = term;

  collectVariableSortsIter(t,map);

  /*
  unsigned position = 0;
  for (TermList* ts = term->args(); ts->isNonEmpty(); ts = ts->next()) {
    collectVariableSorts(*ts, getArgSort(term, position++), map);
  }
  */

} // SortHelper::collectVariableSorts

/**
 * Context sort is needed for FOOL support. For some of the special terms,
 * the sort of the occurrence of a variable cannot be derived from the functor.
 * Example: $let(f := c, X). Here the sort of X is the sort of the occurence of
 * the $let-term, therefore we need to pass the context around explicitly.
 */
void SortHelper::collectVariableSorts(TermList ts, TermList contextSort, DHMap<unsigned,TermList>& map)
{
  CALL("SortHelper::collectVariableSorts(TermList,...)");

  CollectTask t;
  t.fncTag = COLLECT_TERMLIST;
  t.ts = ts;
  t.contextSort = contextSort;

  collectVariableSortsIter(t,map);

  /*
  if (ts.isTerm()) {
    Term* term = ts.term();
    if (term->isSpecial()) {
      collectVariableSortsSpecialTerm(term, contextSort, map);
    } else {
      collectVariableSorts(term, map);
    }
  } else if (ts.isOrdinaryVar()) {
    unsigned var = ts.var();
    if (!map.insert(var, contextSort)) {
      ASS_EQ(contextSort, map.get(var));
    }
  }
  */
} // SortHelper::collectVariableSorts

/*void SortHelper::collectVariableSortsSpecialTerm(Term* term, unsigned contextSort, DHMap<unsigned,unsigned>& map) {
  CALL("SortHelper::collectVariableSortsSpecialTerm(Term*,...)");

  CollectTask task;
  task.fncTag = COLLECT_SPECIALTERM;
  task.t = term;
  task.contextSort = contextSort;

  collectVariableSortsIter(task,map);
   */
  /*
  ASS(term->isSpecial());

  Stack<TermList*> ts(0);

  Term::SpecialTermData* sd = term->getSpecialData();

  switch (term->functor()) {
    case Term::SF_ITE: {
      collectVariableSorts(sd->getCondition(), map);

      ts.push(term->nthArgument(0));
      ts.push(term->nthArgument(1));
      break;
    }

    case Term::SF_LET: {
      TermList binding = sd->getBinding();
      bool isPredicate = binding.isTerm() && binding.term()->isBoolean();
      Signature::Symbol* symbol = isPredicate ? env.signature->getPredicate(sd->getFunctor())
                                              : env.signature->getFunction(sd->getFunctor());
      unsigned position = 0;
      Formula::VarList::Iterator vit(sd->getVariables());
      while (vit.hasNext()) {
        unsigned var = (unsigned)vit.next();
        unsigned sort = isPredicate ? symbol->predType()->arg(position) : symbol->fnType()->arg(position);
        if (!map.insert(var, sort)) {
          ASS_EQ(sort, map.get(var));
        }
        position++;
      }

      if (isPredicate) {
        ts.push(&binding);
      } else {
        collectVariableSorts(binding, symbol->fnType()->result(), map);
      }

      ts.push(term->nthArgument(0));
      break;
    }

    case Term::SF_LET_TUPLE: {
      TermList binding = sd->getBinding();
      Signature::Symbol* symbol = env.signature->getFunction(sd->getFunctor());
      collectVariableSorts(binding, symbol->fnType()->result(), map);
      ts.push(term->nthArgument(0));
      break;
    }

    case Term::SF_FORMULA:
      collectVariableSorts(sd->getFormula(), map);
      break;

    case Term::SF_TUPLE:
      collectVariableSorts(sd->getTupleTerm(), map);
      break;

#if VDEBUG
    default:
      ASSERTION_VIOLATION;
#endif
  }

  Stack<TermList*>::Iterator tit(ts);
  while (tit.hasNext()) {
    collectVariableSorts(*tit.next(), contextSort, map);
  }
  
} */// SortHelper::collectVariableSortsSpecialTerm

/**
 * Insert variable sorts from @c f into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Formula* f, DHMap<unsigned,TermList>& map)
{
  CALL("SortHelper::collectVariableSorts(Formula*,...)");

  CollectTask task;
  task.fncTag = COLLECT_FORMULA;
  task.f = f;

  collectVariableSortsIter(task,map);
}

/**
 * Insert variable sorts from @c u into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Unit* u, DHMap<unsigned,TermList>& map)
{
  CALL("SortHelper::collectVariableSorts(Unit*,...)");

  if (!u->isClause()) {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);

    CollectTask task;
    task.fncTag = COLLECT_FORMULA;
    task.f = fu->formula();

    collectVariableSortsIter(task,map);

    return;
  }

  Clause* cl = static_cast<Clause*>(u);
  Clause::Iterator cit(*cl);
  while (cit.hasNext()) {
    Literal* l = cit.next();

    CollectTask task;
    task.fncTag = COLLECT_TERM;
    task.t = l;

    collectVariableSortsIter(task,map);
  }
}

/**
 * If variable @c var occurrs in term @c t, set @c result to its
 * sort and return true. Otherwise return false.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 */
bool SortHelper::tryGetVariableSort(TermList var, Term* t0, TermList& result)
{
  CALL("SortHelper::tryGetVariableSort");
  ASS(var.isVar());

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    Term* t = sit.next().term();
    /*if(t->isLet()){
      TermList binding = t->getSpecialData()->getBinding();
      if(binding.isVar()) {
        if ( binding == var) {
          // get result sort of the functor
          unsigned f = t->getSpecialData()->getFunctor();
          Signature::Symbol* sym = env.signature->getFunction(f);
          return sym->fnType()->result();
        }
      } else if(tryGetVariableSort(var,binding.term(),result)){
        return true;
      }

      ASS_EQ(t->arity(),1);
      if (*t->nthArgument(0) == var) {
        result = t->getSpecialData()->getSort();
        return true;
      }

      continue;
    }
    if (t->isITE()) {
      // if its in the condition, it is in a subformula to be iterated over by tryGetVariableSort(unsigned var, Formula* f, ...
      ASS_EQ(t->arity(),2);
      if (*t->nthArgument(0) == var || *t->nthArgument(1) == var) {
        result = t->getSpecialData()->getSort();
        return true;
      }
      continue;
    }*/
    if (t->isLambda()) {
      TermList sort = t->getSpecialData()->getLambdaExpSort();
      TermList lambdaTerm = t->getSpecialData()->getLambdaExp();

      if(lambdaTerm.isTerm()){
        if(tryGetVariableSort(var, lambdaTerm.term(),result)){
          return true;
        }
      } else {
        if(lambdaTerm == var){
          result = sort;
          return true;
        }
      }
      continue;
    }
    if (t->shared() && t->ground()) {
      sit.right();
      continue;
    }
    int idx = 0;
    TermList* args = t->args();
    while (!args->isEmpty()) {
      if (*args==var) {
        result = getArgSort(t, idx);
        return true;
      }
      idx++;
      args=args->next();
    }
  }
  return false;
} // SortHelper::tryGetVariableSort

/**
 * Return true iff sorts of immediate subterms of term/literal @c t correspond
 * to the type of @c t.
 *
 * @pre Arguments of t must be shared.
 */
bool SortHelper::areImmediateSortsValid(Term* t)
{
  CALL("SortHelper::areImmediateSortsValid");

  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    Literal* lit = static_cast<Literal*>(t);
    TermList eqSrt = getEqualityArgumentSort(lit);
    for (unsigned i=0; i<2; i++) {
      TermList arg = *t->nthArgument(i);
      if (!arg.isTerm()) { continue; }
      Term* ta = arg.term();
      TermList argSort = getResultSort(ta);
      if (eqSrt != argSort) {
        return false;
      }
    }
    return true;
  }
    
  if(isSuper(t)){ return true; }
  
  OperatorType* type = getType(t);
  unsigned arity = t->arity();
  Substitution subst;
  getTypeSub(t, subst);
  for (unsigned i=0; i<arity; i++) {
    TermList arg = *t->nthArgument(i);
    if (!arg.isTerm()) { continue; }
    Term* ta = arg.term();
    TermList argSort = getResultSort(ta);
    TermList instantiatedTypeSort = SubstHelper::apply(type->arg(i), subst);
    if (instantiatedTypeSort != argSort) { //TODO problem here?
      cout << "the term is " + t->toString() << endl;
      cout << "the type of function " + env.signature->getFunction(t->functor())->name() + " is: " + type->toString() << endl;
      //cout << "function name : "+ env.signature->getFunction(t->functor())->name() << endl;
      //cout << "function name 2 :" + t->functionName() << endl;
      cout << "error with expected " << instantiatedTypeSort.toString() << " and actual " << argSort.toString() << " when functor is " << t->functor() << " and arg is " << arg << endl;
      return false;
    }
  }
  return true;
}

/**
 * Return true iff sorts of all terms (both functions and variables) match
 * in clause @c cl.
 *
 * There should not be any clause for which would this function return false.
 */
bool SortHelper::areSortsValid(Clause* cl)
{
  CALL("SortHelper::areSortsValid");

  static DHMap<unsigned,TermList> varSorts;
  varSorts.reset();

  unsigned clen = cl->length();
  for (unsigned i=0; i<clen; i++) {
    if (!areSortsValid((*cl)[i], varSorts)) {
      return false;
    }
  }
  return true;
}

/**
 * Return true iff the argument sorts are valid in term or literal @c t0.
 * @c varSorts contains sorts of variables -- this map is used to check sorts of variables in the
 * term, and also is extended by sorts of variables that occurr for the first time.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 */
bool SortHelper::areSortsValid(Term* t0, DHMap<unsigned,TermList>& varSorts)
{
  CALL("SortHelper::areSortsValid");

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    Term* t = sit.next().term();
    int idx = 0;
    TermList* args = t->args();
    while (!args->isEmpty()) {
      TermList argSrt = getArgSort(t,idx);
      TermList arg = *args;
      if (arg.isVar()) {
        TermList varSrt;
        if (!varSorts.findOrInsert(arg.var(), varSrt, argSrt)) {
          //the variable is not new
          if (varSrt != argSrt) {
            return false;
          }
        }
      } else {
        if (argSrt != getResultSort(arg.term())) {
          return false;
        }
      }
      idx++;
      args=args->next();
    }
  }
  return true;
} // areSortsValid 

bool SortHelper::isSuper(Term* t){
  CALL("isSuper");
  
  return (!t->isLiteral() && (env.signature->getFunction(t->functor())->name() == "'$tType'"));
 
}
