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
 * @file SortHelper.cpp
 * Implements class SortHelper.
 */

#include "Lib/Environment.hpp"
#include "Lib/MultiCounter.hpp"

#include "Clause.hpp"
#include "FormulaUnit.hpp"
#include "Signature.hpp"
#include "OperatorType.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Substitution.hpp"
#include "SubstHelper.hpp"

#include "SortHelper.hpp"

using namespace std;
using namespace Kernel;


/**
 * Return the type of a term or a literal @c t
 * @author Andrei Voronkov
 */
OperatorType* SortHelper::getType(Term const* t)
{
  if (t->isLiteral()) {
    return env.signature->getPredicate(t->functor())->predType();
  } else if (t->isSort()) {
    return env.signature->getTypeCon(t->functor())->typeConType();
  }
  return env.signature->getFunction(t->functor())->fnType();
} // getType

/**
 * This function achieves the following. Let t = f<a1, a2>(t1, t2)
 * where ai are type arguments and ti are terms arguments. Let f have
 * type !>[X, Y]: (s1 * s2) > s3. The function returns the subsitution
 * \sigma = [X -> a1, Y -> a2]. The type of t is is s3\sigma, the type of
 * t1 s1\sigma and the type of t2 s2\sigma 
 * 
 * @author Ahmed Bhayat
 */
void SortHelper::getTypeSub(const Term* t, Substitution& subst)
{
  TermList* typeArg;
  OperatorType* ot       = getType(const_cast<Term*>(t)); //sym->fnType();
  unsigned typeArgsArity = ot->numTypeArguments();
  //cout << "typeArgsArity " << typeArgsArity << endl;

  typeArg = const_cast<TermList*>(t->args());
  for(unsigned i = 0; i < typeArgsArity; i++){
    TermList var = ot->quantifiedVar(i);
    ASS_REP(var.isVar(), t->toString());
    subst.bind(var.var(), *typeArg);
    typeArg = typeArg->next();
  }  
} // getTypeSub

/**
 * Return the sort of a non-variable term t. This function cannot be applied
 * to a special term, such as if-then-else.
 *
 * The return sort is calculated by applying the relavant type substitution
 * to return sort of the type of the head symbol of t. For monomorphic problems,
 * it is more efficient to use getResultSortMono since the substitution will always
 * be empty.
 */
TermList SortHelper::getResultSort(const Term* t)
{
  ASS(!t->isSpecial());
  ASS(!t->isLiteral());

  if(t->isSort()){
    return TermList(AtomicSort::superSort());
  }

  Substitution subst;
  getTypeSub(t, subst);
  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  TermList result = sym->fnType()->result();

  /*
  either
  1. the substitution is non-empty
  2. the result is ground (or $tType)
  3. t is let-bound: consider the following TFF1

      % polymorphic constant
      tff(c_type, type, c: !>[A: $tType]: A).
      % some polymorphic predicate, not important
      tff(p_type, type, p: !>[A: $tType]: A > $o).

      % let-bind a polymorphic identity function
      tff(bug, axiom, ![A: $tType]: $let(id: A > A, id(X) := X, p(A, id(c(A))))).
      % note that type of id is A > A, *not* !>[A: $tType]: A > A.
  */
  ASS(
    !subst.isEmpty() ||
    (result.isTerm() && (result.term()->isSuper() || result.term()->ground())) ||
    sym->letBound()
  )
  return SubstHelper::apply(result, subst);
}

TermList SortHelper::getResultSortMono(const Term* t)
{
  ASS(!t->isSpecial());
  ASS(!t->isLiteral());

  Signature::Symbol* sym = env.signature->getFunction(t->functor());
  return sym->fnType()->result();
}

/**
 * Try get result sort of a term.
 *
 * This function can be applied also to special terms such as if-then-else.
 */
bool SortHelper::tryGetResultSort(const Term* t, TermList& result)
{
  ASS(!t->isLiteral());

  TermList masterVar;
  return getResultSortOrMasterVariable(t, result, masterVar);
}

bool SortHelper::tryGetResultSort(const TermList t, TermList& result)
{
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
  if(t->isSort()){
    resultSort = AtomicSort::superSort();
    return true;
  }

  if (!t->isSpecial()) {
      resultSort = getResultSort(t);
      return true;
  }

  switch(t->specialFunctor()) {
    case SpecialFunctor::LET:
    case SpecialFunctor::LET_TUPLE:
    case SpecialFunctor::ITE:
    case SpecialFunctor::MATCH:
      resultSort = t->getSpecialData()->getSort();
      return true;
    case SpecialFunctor::FORMULA:
      resultSort = AtomicSort::boolSort();
      return true;
    case SpecialFunctor::LAMBDA: {
      resultSort = t->getSpecialData()->getSort();
      return true;
    }
    case SpecialFunctor::TUPLE: {
      resultSort = getResultSort(t->getSpecialData()->getTupleTerm());
      return true;
    }
  }
  ASSERTION_VIOLATION
  
} // SortHelper::getResultSortOrMasterVariable

/**
 * If sort of term @c t depends on a variable, assign the variable into
 * @c resultVar and return false. Otherwise assign the sort of the term
 * into @c resultSort and return true.
 */
bool SortHelper::getResultSortOrMasterVariable(const TermList t, TermList& resultSort, TermList& resultVar)
{
  if (t.isVar()) {
    resultVar = t;
    return false;
  }
  return getResultSortOrMasterVariable(t.term(), resultSort, resultVar);
}

/**
 * Return sort of the argument @c argIndex of the term or literal @c t
 */
TermList SortHelper::getArgSort(Term const* t, unsigned argIndex)
{
  ASS_L(argIndex, t->arity());

  if(t->isSort()){
    return AtomicSort::superSort();
  }

  if (t->isLiteral() && static_cast<Literal const*>(t)->isEquality()) {
    return getEqualityArgumentSort(static_cast<Literal const*>(t));
  }

  Substitution subst;
  OperatorType* ot = getType(t);

  if(argIndex < ot->numTypeArguments()){
    return AtomicSort::superSort();
  }
  
  getTypeSub(t, subst);
  return SubstHelper::apply(ot->arg(argIndex), subst);
} // getArgSort

/* returns the sort of the nth term argument */
TermList SortHelper::getTermArgSort(Term const* t, unsigned n)
{ return getArgSort(t, n + t->numTypeArguments()); }

TermList SortHelper::getEqualityArgumentSort(const Literal* lit)
{
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
  TermList res;
  ALWAYS(tryGetVariableSortTerm(var, t, res, true));
  return res;
}

/**
 * Return sort of variable @c var in formula @c f.
 *
 * The variable
 */
bool SortHelper::tryGetVariableSort(unsigned var, Formula* f, TermList& res)
{
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
      if(tryGetVariableSortTerm(varTerm, lit, res, false)){
        return true;
      }
    }
    if(sf->connective() == BOOL_TERM){
      TermList stt = sf->getBooleanTerm();
      if(stt.isVar() && stt.var()==var){
        res = AtomicSort::boolSort();
        return true;
      }
      if(stt.isTerm()){
        Term* st = stt.term();
        if(tryGetVariableSortTerm(varTerm,st,res, false)){
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
void SortHelper::collectVariableSortsIter(CollectTask task, DHMap<unsigned,TermList>& map, bool ignoreBound)
{
  Stack<CollectTask> todo;
  MultiCounter bound;

  todo.push(task);
  while (todo.isNonEmpty()) {
    CollectTask task = todo.pop();

    switch(task.fncTag) {
      case COLLECT_TERM: {
        Term* term = task.t;
    
        unsigned position = 0;
        for (TermList* ts = term->args(); ts->isNonEmpty(); ts = ts->next()) {
          CollectTask newTask(COLLECT_TERMLIST);
          newTask.ts = *ts;
          newTask.contextSort = getArgSort(term, position++);
          todo.push(newTask);
        }

      } break;

      case COLLECT_TERMLIST: {
        TermList ts = task.ts;

        if (ts.isTerm()) {
          Term* term = ts.term();

          CollectTask newTask(term->isSpecial() ? COLLECT_SPECIALTERM : COLLECT_TERM);
          newTask.t = term;
          newTask.contextSort = task.contextSort;
          todo.push(newTask);
        } else if (ts.isOrdinaryVar()) {
          unsigned var = ts.var();
          if (!ignoreBound || !bound.get(var)) {
            if (!map.insert(var, task.contextSort)) {
              ASS_EQ(task.contextSort, map.get(var));
            }
          }
        }

      } break;

      case COLLECT_SPECIALTERM: {
        Term* term = task.t;

        ASS(term->isSpecial());

        Term::SpecialTermData* sd = term->getSpecialData();

        switch (term->specialFunctor()) {
          case SpecialFunctor::ITE: {
            CollectTask newTask(COLLECT_TERMLIST);
            newTask.contextSort = sd->getSort();

            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.ts = *term->nthArgument(1);
            todo.push(newTask);

            newTask.fncTag = COLLECT_FORMULA;
            newTask.f = sd->getCondition();
            todo.push(newTask);

            break;
          }

          case SpecialFunctor::LET: {
            TermList binding = sd->getBinding();
            bool isPredicate = binding.isTerm() && binding.term()->isBoolean();
            Signature::Symbol* symbol = isPredicate ? env.signature->getPredicate(sd->getFunctor())
                                                    : env.signature->getFunction(sd->getFunctor());
            VList::Iterator vit(sd->getVariables());
            Substitution subst;
            auto type = isPredicate ? symbol->predType() : symbol->fnType();
            for (unsigned i = 0; i < type->arity(); i++) {
              ASS(vit.hasNext());
              auto var = vit.next();
              TermList sort = AtomicSort::superSort();
              if (i < type->numTypeArguments()) {
                subst.bind(type->quantifiedVar(i).var(), TermList(var, false));
              } else {
                sort = SubstHelper::apply(type->arg(i),subst);
              }
              if (!ignoreBound || !bound.get(var)) {
                if (!map.insert(var, sort)) {
                  ASS_EQ(sort, map.get(var));
                }
              }
            }

            CollectTask newTask(COLLECT_TERMLIST);
            newTask.contextSort = sd->getSort();

            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.ts = binding;
            if (!isPredicate) {
              newTask.contextSort = SubstHelper::apply(type->result(),subst);
            }
            todo.push(newTask);

            break;
          }

          case SpecialFunctor::LET_TUPLE: {
            TermList binding = sd->getBinding();
            Signature::Symbol* symbol = env.signature->getFunction(sd->getFunctor());
            Substitution subst;
            VList::Iterator vit(sd->getTupleSymbols());
            auto type = symbol->fnType();
            for (unsigned i = 0; i < type->arity(); i++) {
              ASS(vit.hasNext());
              auto var = vit.next();
              TermList sort = AtomicSort::superSort();
              if (i < type->numTypeArguments()) {
                subst.bind(type->quantifiedVar(i).var(), TermList(var, false));
              } else {
                sort = SubstHelper::apply(type->arg(i),subst);
              }
              if (!ignoreBound || !bound.get(var)) {
                if (!map.insert(var, sort)) {
                  ASS_EQ(sort, map.get(var));
                }
              }
            }

            CollectTask newTask(COLLECT_TERMLIST);
            newTask.contextSort = sd->getSort();
            newTask.ts = *term->nthArgument(0);
            todo.push(newTask);

            newTask.contextSort = SubstHelper::apply(type->result(),subst);
            newTask.ts = binding;
            todo.push(newTask);

            break;
          }

          case SpecialFunctor::FORMULA: {
            CollectTask newTask(COLLECT_FORMULA);
            newTask.f = sd->getFormula();
            todo.push(newTask);
          } break;
          case SpecialFunctor::LAMBDA: {
            CollectTask newTask(COLLECT_TERMLIST);
            newTask.contextSort = sd->getLambdaExpSort();
            newTask.ts = sd->getLambdaExp();
            todo.push(newTask);
          } break;

          case SpecialFunctor::TUPLE: {
            CollectTask newTask(COLLECT_TERM);
            newTask.t = sd->getTupleTerm();
            todo.push(newTask);
          } break;

          case SpecialFunctor::MATCH: {
            CollectTask newTask(COLLECT_TERMLIST);
            auto matchedSort = term->getSpecialData()->getMatchedSort();

            // there are two sorts here, one is the sort
            // of matched term and patterns, the other is
            // the sort of the match block and of each case
            newTask.ts = *term->nthArgument(0);
            newTask.contextSort = matchedSort;
            todo.push(newTask);
            for (unsigned int i = 1; i < term->arity(); i += 2) {
              newTask.ts = *term->nthArgument(i);
              newTask.contextSort = matchedSort;
              todo.push(newTask);

              newTask.ts = *term->nthArgument(i + 1);
              newTask.contextSort = sd->getSort();
              todo.push(newTask);
            }
            break;
          }
        }
      } break;

      case COLLECT_FORMULA: {
        Formula* f = task.f;

        switch (f->connective()) {
          case LITERAL: {
            Literal* lit = f->literal();
            if(lit->isTwoVarEquality()){
              CollectTask newTask(COLLECT_TERMLIST);
              newTask.ts = lit->twoVarEqSort();
              newTask.contextSort = AtomicSort::superSort();
              todo.push(newTask);
            }
            CollectTask newTask(COLLECT_TERM);
            newTask.t = lit;

            todo.push(newTask);
            break;
          }

          case BOOL_TERM: {
            TermList ts = f->getBooleanTerm();
            if (ts.isVar()) {
              if (!ignoreBound || !bound.get(ts.var())) {
                if (!map.insert(ts.var(), AtomicSort::boolSort())) {
                  ASS_EQ(AtomicSort::boolSort(), map.get(ts.var()));
                }
              }
            } else {
              ASS(ts.isTerm());

              CollectTask newTask(ts.term()->isSpecial() ? COLLECT_SPECIALTERM : COLLECT_TERM);
              newTask.t = ts.term();
              newTask.contextSort = AtomicSort::boolSort();

              todo.push(newTask);
            }
            break;
          }

          case EXISTS:
          case FORALL: {
            if (ignoreBound) {
              CollectTask unbindTask(UNBIND);
              unbindTask.vars = f->vars();
              todo.push(unbindTask);
            }

            CollectTask newTask(COLLECT_FORMULA);
            newTask.f = f->qarg();
            todo.push(newTask);

            if (ignoreBound) {
              CollectTask bindTask(BIND);
              bindTask.vars = f->vars();
              todo.push(bindTask);
            }
            break;
          }

          case AND:
          case OR: {
            FormulaList::Iterator argIt(f->args());
            while (argIt.hasNext()) {
              CollectTask newTask(COLLECT_FORMULA);
              newTask.f = argIt.next();
              todo.push(newTask);
            }
            break;
          }

          case IMP:
          case IFF:
          case XOR: {
            CollectTask leftTask(COLLECT_FORMULA);
            leftTask.f = f->left();
            todo.push(leftTask);

            CollectTask rightTask(COLLECT_FORMULA);
            rightTask.f = f->right();
            todo.push(rightTask);
            break;
          }

          case NOT: {
            CollectTask newTask(COLLECT_FORMULA);
            newTask.f = f->uarg();
            todo.push(newTask);
            break;
          }

          default:
            continue;
        }
      } break;

      case BIND: {
        VList::Iterator vit(task.vars);
        while (vit.hasNext()) {
          bound.inc(vit.next());
        }
      } break;

      case UNBIND: {
        VList::Iterator vit(task.vars);
        while (vit.hasNext()) {
          bound.dec(vit.next());
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
  CollectTask t(term->isSpecial() ? COLLECT_SPECIALTERM : COLLECT_TERM);
  t.t = term;

  collectVariableSortsIter(t,map);
} // SortHelper::collectVariableSorts

/**
 * Insert variable sorts from @c f into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Formula* f, DHMap<unsigned,TermList>& map, bool ignoreBound)
{
  CollectTask task(COLLECT_FORMULA);
  task.f = f;

  collectVariableSortsIter(task,map,ignoreBound);
}

/**
 * Insert variable sorts from @c u into @c map. If a variable
 * is in map already (or appears multiple times), assert that
 * the sorts are equal.
 */
void SortHelper::collectVariableSorts(Unit* u, DHMap<unsigned,TermList>& map)
{
  if (!u->isClause()) {
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);

    CollectTask task(COLLECT_FORMULA);
    task.f = fu->formula();

    collectVariableSortsIter(task,map);

    return;
  }

  Clause* cl = static_cast<Clause*>(u);
  for (Literal* l : cl->iterLits()) {

    CollectTask task(COLLECT_TERM);
    task.t = l;

    collectVariableSortsIter(task,map);
  }
}

void SortHelper::normaliseArgSorts(VList* qVars, TermStack& argSorts)
{
  Substitution subst;
  unsigned i = 0;
  while(qVars){
    unsigned var = qVars->head();
    subst.bind(var, TermList(i++, false));
    qVars = qVars->tail();
  }

  for(unsigned i = 0; i < argSorts.size(); i++){
    argSorts[i] = SubstHelper::apply(argSorts[i], subst);
  }
}

void SortHelper::normaliseSort(VList* qVars, TermList& sort)
{
  Substitution subst;
  unsigned i = 0;
  while(qVars){
    unsigned var = qVars->head();
    subst.bind(var, TermList(i++, false));
    qVars = qVars->tail();
  }

  sort = SubstHelper::apply(sort, subst);
}

void SortHelper::normaliseArgSorts(TermStack& qVars, TermStack& argSorts)
{
  Substitution subst;
  for(unsigned i = 0; i < qVars.size(); i++){
    subst.bind(qVars[i].var(), TermList(i, false));
  }

  for(unsigned i = 0; i < argSorts.size(); i++){
    argSorts[i] = SubstHelper::apply(argSorts[i], subst);
  }
}

void SortHelper::normaliseSort(TermStack qVars, TermList& sort)
{
  Substitution subst;
  for(unsigned i = 0; i < qVars.size(); i++){
    subst.bind(qVars[i].var(), TermList(i, false));
  }

  sort = SubstHelper::apply(sort, subst);
}

/**
 * If variable @c var occurrs in term @c t, set @c result to its
 * sort and return true. Otherwise return false.
 * @since 04/05/2013 Manchester, new NonVariableIterator is used
 * @author Andrei Voronkov
 *
 * MS: Note that tryGetVariableSortTerm is typically called by tryGetVariableSort(unsigned,Formula*,unsigned&) which
 *   traverses all subformulas, including those in special terms! If those invocations of tryGetVariableSortTerm
 *   would again go after these subformulas, nested useless calls could arise.
 */
bool SortHelper::tryGetVariableSortTerm(TermList var, Term* t0, TermList& result, bool recurseToSubformulas)
{
  ASS(var.isVar());

  NonVariableIterator sit(t0,true);
  while (sit.hasNext()) {
    Term* t = sit.next().term();
    if(t->isLet()){
      TermList binding = t->getSpecialData()->getBinding();
      if(binding.isVar()) {
        if ( binding == var) {
          // get result sort of the functor
          unsigned f = t->getSpecialData()->getFunctor();
          Signature::Symbol* sym = env.signature->getFunction(f);
          result = sym->fnType()->result();
          return true;
        }
      } else if(tryGetVariableSortTerm(var,binding.term(),result,recurseToSubformulas)){
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
      if (recurseToSubformulas) {
        Formula* f = t->getSpecialData()->getCondition();
        if(tryGetVariableSort(var.var(), f, result)){
          return true;
        }
      }
      ASS_EQ(t->arity(),2);
      if (*t->nthArgument(0) == var || *t->nthArgument(1) == var) {
        result = t->getSpecialData()->getSort();
        return true;
      }
      continue;
    }
    if(t->isFormula() && recurseToSubformulas){
      Formula* f = t->getSpecialData()->getFormula();
      if(tryGetVariableSort(var.var(), f, result)){
        return true;
      }
    }
    if (t->isLambda()) {
      TermList sort = t->getSpecialData()->getLambdaExpSort();
      TermList lambdaTerm = t->getSpecialData()->getLambdaExp();

      if(lambdaTerm.isTerm()){
        if(tryGetVariableSortTerm(var, lambdaTerm.term(),result,recurseToSubformulas)){
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
    if (t->isMatch()) {
      for (unsigned int i = 0; i < t->arity(); i++) {
        auto arg = t->nthArgument(i);
        if (*arg == var && tryGetResultSort(*arg, result)) {
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
//      cout << "The arg is " + args->toString() << endl;
//      cout << "the var is " + var.toString() << endl;
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
bool SortHelper::areImmediateSortsValidPoly(Term* t)
{
  ASS(!t->isSuper());  

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
    if (instantiatedTypeSort != argSort) {
      return false;
    }
  }
  return true;
}


/**
 * Return true iff sorts of immediate subterms of term/literal @c t correspond
 * to the type of @c t.
 *
 * @pre Arguments of t must be shared.
 */
bool SortHelper::areImmediateSortsValidMono(Term* t)
{
  ASS(!t->isSuper());  

  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    Literal* lit = static_cast<Literal*>(t);
    TermList eqSrt = getEqualityArgumentSort(lit);
    for (unsigned i=0; i<2; i++) {
      TermList arg = *t->nthArgument(i);
      if (!arg.isTerm()) { continue; }
      Term* ta = arg.term();
      TermList argSort = getResultSortMono(ta);
      if (eqSrt != argSort) {
        return false;
      }
    }
    return true;
  }

  OperatorType* type = getType(t);
  unsigned arity = t->arity();
  for (unsigned i=0; i<arity; i++) {
    TermList arg = *t->nthArgument(i);
    if (!arg.isTerm()) { continue; }
    Term* ta = arg.term();
    TermList argSort = getResultSortMono(ta);
    if (type->arg(i) != argSort) {
      //cout << "error with expected " << type.arg(i) << " and actual " << argSort << " when functor is " << t->functor() << " and arg is " << arg << endl;
      return false;
    }
  }
  return true;
}

/**
 * Return true iff immediate subterms of sort @c sort are all
 * sorts
 *
 * @pre Arguments of sorts must be shared.
 */
bool SortHelper::allTopLevelArgsAreSorts(AtomicSort* sort)
{
  for(unsigned i = 0; i < sort->arity(); i++){
    TermList arg = *sort->nthArgument(i);
    if(arg.isVar()){
      continue;
    }
    if(!arg.term()->isSort()){
      return false;
    }
  }
  return true;
}

TermList SortHelper::getIndexSort(TermList arraySort)
{
  ASS(arraySort.isArraySort());
  return *arraySort.term()->nthArgument(0);
}

TermList SortHelper::getInnerSort(TermList arraySort)
{
  ASS(arraySort.isArraySort());
  return *arraySort.term()->nthArgument(1);
}

/**
 * Return true iff sorts of all terms (both functions and variables) match
 * in clause @c cl.
 *
 * There should not be any clause for which would this function return false.
 */
bool SortHelper::areSortsValid(Clause* cl)
{
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
bool SortHelper::areSortsValid(Term* t0)
{
  DHMap<unsigned,TermList> varSorts;
  return areSortsValid(t0, varSorts);
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
