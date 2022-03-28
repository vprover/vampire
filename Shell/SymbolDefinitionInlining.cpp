/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Substitution.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/SortHelper.hpp"

#include "SymbolDefinitionInlining.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

TermList SymbolDefinitionInlining::substitute(Term::Iterator tit) {
  CALL("SymbolDefinitionInlining::substitute");

  Substitution substitution;

  VList::Iterator vit(_bindingVariables);
  while (vit.hasNext()) {
    unsigned var = vit.next();
    ASS(tit.hasNext());
    TermList arg = tit.next();
    substitution.bind(var, arg);
  }
  ASS(!tit.hasNext());

  if (_counter > 0) {
    /**
     * The _binding is inlined more than once. In such case, rename it's bound
     * variables.
     */

    if (_counter == 1) {
      /**
       * The second occurrence of the _binding -- need to calculate it's bound variables.
       *
       * TODO: This is insufficient to cover the case when a variable is bound
       * multiple times in nested expressions. This is left as is for now,
       * because this case cannot occur with let-bindings of constant.
       */
      collectBoundVariables(_binding);
    }

    VList::Iterator bit(_bound);
    while (bit.hasNext()) {
      unsigned boundVar = bit.next();
      unsigned freshVar = ++_freshVarOffset;
      substitution.bind(boundVar, TermList(freshVar, false));
      List<pair<unsigned, unsigned>>::push(make_pair(boundVar, freshVar), _varRenames);
    }
  }

  _counter++;

  return SubstHelper::apply(_binding, substitution);
}

TermList SymbolDefinitionInlining::process(TermList ts) {
  CALL("SymbolDefinitionInlining::process(TermList)");

  if (ts.isVar()) {
    return ts;
  }

  Term* term = ts.term();

  if (term->isSpecial()) {
    Term::SpecialTermData *sd = term->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        Formula* formula = process(sd->getFormula());

        if (formula == sd->getFormula()) {
          return ts;
        }

        return TermList(Term::createFormula(formula));
      }

      case Term::SF_ITE: {
        Formula* condition  = process(sd->getCondition());
        TermList thenBranch = process(*term->nthArgument(0));
        TermList elseBranch = process(*term->nthArgument(1));

        if ((condition == sd->getCondition()) && (thenBranch == *term->nthArgument(0)) && (elseBranch == *term->nthArgument(1))) {
          return ts;
        }

        return TermList(Term::createITE(condition, thenBranch, elseBranch, sd->getSort()));
      }

      case Term::SF_LET: {
        TermList binding = process(sd->getBinding());
        TermList body = process(*term->nthArgument(0));

        if ((sd->getBinding() == binding) && (*term->nthArgument(0) == body)) {
          return ts;
        }

        return TermList(Term::createLet(sd->getFunctor(), sd->getVariables(),
                                        binding, body, sd->getSort()));
      }

      case Term::SF_LET_TUPLE: {
        TermList binding = process(sd->getBinding());
        TermList body = process(*term->nthArgument(0));

        if ((sd->getBinding() == binding) && (*term->nthArgument(0) == body)) {
          return ts;
        }

        return TermList(Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(),
                                             binding, body, sd->getSort()));
      }

      case Term::SF_TUPLE: {
        TermList tuple = process(TermList(sd->getTupleTerm()));
        ASS(tuple.isTerm());

        Term* t = tuple.term();
        if (t == sd->getTupleTerm()) {
          return ts;
        }

        // Replace [$proj(0, t), ..., $proj(n, t)] with t
        TermList tupleConstant;
        if (mirroredTuple(t, tupleConstant)) {
          return tupleConstant;
        }

        return TermList(Term::createTuple(t));
      }

      case Term::SF_MATCH: {
        DArray<TermList> terms(term->arity());
        bool unchanged = true;
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = process(*term->nthArgument(i));
          unchanged = unchanged && (terms[i] == *term->nthArgument(i));
        }

        if (unchanged) {
          return ts;
        }
        return TermList(Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin()));
      }

      default:
        ASSERTION_VIOLATION_REP(term->toString());
    }
  }

  Term::Iterator terms(term);

  if (!_isPredicate && (term->functor() == _symbol)) {
    return substitute(terms);
  }

  bool substituted = false;
  Stack<TermList> args;
  while (terms.hasNext()) {
    TermList argument = terms.next();
    TermList processedArgument = process(argument);
    if (argument != processedArgument) {
      substituted = true;
    }
    args.push(processedArgument);
  }

  if (!substituted) {
    return ts;
  }

  return TermList(Term::create(term, args.begin()));
}

bool SymbolDefinitionInlining::mirroredTuple(Term* tuple, TermList &tupleConstant) {
  bool foundTupleConstant = false;
  TermList tupleSort = env.signature->getFunction(tuple->functor())->fnType()->result();
  ASS(tupleSort.isTupleSort());
  for (unsigned i = 0; i < tuple->arity(); i++) {
    if (!tuple->nthArgument(i)->isTerm()) {
      return false;
    }
    Term* arg = (tuple->nthArgument(i))->term();
    TermList possibleTupleConstant;
    if (arg->isSpecial()) {
      if (arg->getSpecialData()->getType() != Term::SF_FORMULA) {
        return false;
      }
      Formula* f = arg->getSpecialData()->getFormula();
      if (f->connective() != LITERAL) {
        return false;
      }
      Literal* l = f->literal();
      if (l->functor() != Theory::tuples()->getProjectionFunctor(i, tupleSort)) {
        return false;
      }
      possibleTupleConstant = *l->nthArgument(0);
    } else {
      if (arg->functor() != Theory::tuples()->getProjectionFunctor(i, tupleSort)) {
        return false;
      }
      possibleTupleConstant = *arg->nthArgument(0);
    }
    if (!possibleTupleConstant.isTerm()) {
      return false;
    }
    if (!foundTupleConstant) {
      tupleConstant = possibleTupleConstant;
      foundTupleConstant = true;
    } else {
      if (possibleTupleConstant != tupleConstant) {
        return false;
      }
    }
  }
  return true;
}

Formula* SymbolDefinitionInlining::process(Formula* formula) {
  CALL("SymbolDefinitionInlining::process(Formula*)");

  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();
      Term::Iterator terms(literal);

      if (_isPredicate && (literal->functor() == _symbol)) {
        if (literal->polarity()) {
          return BoolTermFormula::create(substitute(terms));
        } else {
          Formula* negation = BoolTermFormula::create(substitute(terms));
          if (negation->connective() == LITERAL) {
            return new AtomicFormula(Literal::complementaryLiteral(negation->literal()));
          } else {
            return new NegatedFormula(negation);
          }
        }
      }

      bool substituted = false;
      Stack<TermList> args;
      while (terms.hasNext()) {
        TermList argument = terms.next();
        TermList processedArgument = process(argument);
        if (argument != processedArgument) {
          substituted = true;
        }
        args.push(processedArgument);
      }

      if (!substituted) {
        return formula;
      }

      return new AtomicFormula(Literal::create(literal, args.begin()));
    }

    case AND:
    case OR: {
      FormulaList* args = process(formula->args());

      if (args == formula->args()) {
        return formula;
      }

      return new JunctionFormula(formula->connective(), args);
    }

    case IMP:
    case IFF:
    case XOR: {
      Formula* left  = process(formula->left());
      Formula* right = process(formula->right());

      if ((left == formula->left()) && (right == formula->right())) {
        return formula;
      }

      return new BinaryFormula(formula->connective(), left, right);
    }

    case NOT: {
      Formula* uarg = process(formula->uarg());

      if (uarg == formula->uarg()) {
        return formula;
      }

      return new NegatedFormula(uarg);
    }

    case FORALL:
    case EXISTS: {
      Formula* qarg = process(formula->qarg());

      if (qarg == formula->qarg()) {
        return formula;
      }

      return new QuantifiedFormula(formula->connective(), formula->vars(), formula->sorts(), qarg);
    }

    case BOOL_TERM: {
      TermList ts = process(formula->getBooleanTerm());

      if (ts == formula->getBooleanTerm()) {
        return formula;
      }

      return new BoolTermFormula(ts);
    }

    case TRUE:
    case FALSE:
      return formula;

    default:
      ASSERTION_VIOLATION;
  }
}

FormulaList* SymbolDefinitionInlining::process(FormulaList* formulas) {
  CALL("SymbolDefinitionInlining::process(FormulaList*)");

  Stack<Formula*> elements(FormulaList::length(formulas));

  bool substituted = false;
  FormulaList::Iterator fit(formulas);
  while (fit.hasNext()) {
    Formula* formula = fit.next();
    Formula* processedFormula = process(formula);

    if (formula != processedFormula) {
      substituted = true;
    }

    elements.push(processedFormula);
  }

  if (!substituted) {
    return formulas;
  }

  Stack<Formula*>::Iterator eit(elements);
  FormulaList* processedFormula = FormulaList::empty();
  FormulaList::pushFromIterator(eit, processedFormula);

  return processedFormula;
}

void SymbolDefinitionInlining::collectBoundVariables(TermList ts) {
  CALL("SymbolDefinitionInlining::collectBoundVariables(TermList)");

  if (ts.isVar()) {
    return;
  }

  collectBoundVariables(ts.term());
}

void SymbolDefinitionInlining::collectBoundVariables(Term* t) {
  CALL("SymbolDefinitionInlining::collectBoundVariables(Term*)");

  if (t->shared()) {
    return;
  }

  if (t->isSpecial()) {
    Term::SpecialTermData* sd = t->getSpecialData();
    switch (sd->getType()) {
      case Term::SF_FORMULA: {
        collectBoundVariables(sd->getFormula());
        break;
      }
      case Term::SF_ITE: {
        collectBoundVariables(sd->getCondition());
        break;
      }
      case Term::SF_LET: {
        collectBoundVariables(sd->getBinding());
        VList::Iterator vit(sd->getVariables());
        VList::pushFromIterator(vit, _bound);
        break;
      }
      case Term::SF_LET_TUPLE: {
        collectBoundVariables(sd->getBinding());
        break;
      }
      case Term::SF_TUPLE: {
        collectBoundVariables(sd->getTupleTerm());
        break;
      }
      case Term::SF_MATCH: {
        // args are handled below
        break;
      }
      default:
        ASSERTION_VIOLATION_REP(t->toString());
    }
  }

  Term::Iterator terms(t);
  while (terms.hasNext()) {
    collectBoundVariables(terms.next());
  }
}

void SymbolDefinitionInlining::collectBoundVariables(Formula* formula) {
  CALL("SymbolDefinitionInlining::collectBoundVariables(Formula*)");

  switch (formula->connective()) {
    case FORALL:
    case EXISTS: {
      collectBoundVariables(formula->qarg());
      VList::Iterator vit(formula->vars());
      VList::pushFromIterator(vit, _bound);
      break;
    }

    case AND:
    case OR: {
      List<Formula*>::Iterator fit(formula->args());
      while (fit.hasNext()) {
        collectBoundVariables(fit.next());
      }
      break;
    }

    case NOT: {
      collectBoundVariables(formula->uarg());
      break;
    }

    case IMP:
    case IFF:
    case XOR: {
      collectBoundVariables(formula->left());
      collectBoundVariables(formula->right());
      break;
    }

    case BOOL_TERM: {
      collectBoundVariables(formula->getBooleanTerm());
      break;
    }

    case LITERAL: {
      collectBoundVariables(formula->literal());
      break;
    }

    default:
      break;
  }
}
