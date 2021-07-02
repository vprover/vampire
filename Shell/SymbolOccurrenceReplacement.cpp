/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Kernel/Formula.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SymbolOccurrenceReplacement.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Term* SymbolOccurrenceReplacement::process(Term* term) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(Term*)");
  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (term->functor()) {
      case Term::SF_ITE:
        return Term::createITE(process(sd->getCondition()), process(*term->nthArgument(0)), process(*term->nthArgument(1)), sd->getSort());

        case Term::SF_LET:
          if (_isPredicate == (sd->getBinding().isTerm() && sd->getBinding().term()->isBoolean())) {
            // function symbols, defined inside $let are expected to be
            // disjoint and fresh symbols are expected to be fresh
            ASS_NEQ(sd->getFunctor(), _symbol);
            //ASS_NEQ(sd->getFunctor(), _freshSymbol);
          }
          return Term::createLet(sd->getFunctor(), sd->getVariables(), process(sd->getBinding()), process(*term->nthArgument(0)), sd->getSort());

        case Term::SF_FORMULA:
          return Term::createFormula(process(sd->getFormula()));

      case Term::SF_LET_TUPLE:
        if (_isPredicate == (sd->getBinding().isTerm() && sd->getBinding().term()->isBoolean())) {
          // function symbols, defined inside $let are expected to be
          // disjoint and fresh symbols are expected to be fresh
          ASS_NEQ(sd->getFunctor(), _symbol);
          //ASS_NEQ(sd->getFunctor(), _freshSymbol);
        }
        return Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(), process(sd->getBinding()), process(*term->nthArgument(0)), sd->getSort());

      case Term::SF_TUPLE:
        return Term::createTuple(process(TermList(sd->getTupleTerm())).term());

      case Term::SF_MATCH: {
        DArray<TermList> terms(term->arity());
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = process(*term->nthArgument(i));
        }
        return Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin());
      }

#if VDEBUG
        default:
          ASSERTION_VIOLATION;
#endif
    }
  }

  bool renaming = !_isPredicate && (term->functor() == _symbol);

  TermList* arg = term->args();
  TermStack arguments;
  Substitution substitution;

  if (renaming) {
    VList::Iterator fvit(_argVars);
    while (fvit.hasNext()) {
      unsigned var = fvit.next();
      substitution.bind(var, process(*arg));
      arg = arg->next();
    }
  } else {
    while (!arg->isEmpty()) {
      arguments.push(process(*arg));
      arg = arg->next();
    }  
  }

  if (renaming) {
    return SubstHelper::apply(_freshApplication, substitution);
  } else {
    return Term::create(term, arguments.begin());
  }
}

TermList SymbolOccurrenceReplacement::process(TermList ts) {
  CALL("SymbolOccurrenceReplacement::process(TermList)");

  if (!ts.isTerm()) {
    return ts;
  }

  return TermList(process(ts.term()));
}

Formula* SymbolOccurrenceReplacement::process(Formula* formula) {
  CALL("SymbolOccurrenceReplacement::process(Formula*)");
  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();

      bool renaming = _isPredicate && (literal->functor() == _symbol);

      TermList* arg = literal->args();
      TermStack arguments;
      Substitution substitution;

      if (renaming) {
        VList::Iterator fvit(_argVars);
        while (fvit.hasNext()) {
          unsigned var = fvit.next();
          substitution.bind(var, process(*arg));
          arg = arg->next();
        }
      } else {
        while (!arg->isEmpty()) {
          arguments.push(process(*arg));
          arg = arg->next();
        }    
      }

      Literal* processedLiteral;
      if (renaming) {
        processedLiteral = SubstHelper::apply(static_cast<Literal*>(_freshApplication), substitution);
        if(!literal->polarity()){
          processedLiteral = Literal::complementaryLiteral(processedLiteral);
        }
      } else {
        processedLiteral = Literal::create(literal, arguments.begin());
      }

      return new AtomicFormula(processedLiteral);
    }

    case AND:
    case OR:
      return new JunctionFormula(formula->connective(), process(formula->args()));

    case IMP:
    case IFF:
    case XOR:
      return new BinaryFormula(formula->connective(), process(formula->left()), process(formula->right()));

    case NOT:
      return new NegatedFormula(process(formula->uarg()));

    case FORALL:
    case EXISTS:
      return new QuantifiedFormula(formula->connective(), formula->vars(), formula->sorts(), process(formula->qarg()));

    case BOOL_TERM:
      return new BoolTermFormula(process(formula->getBooleanTerm()));

    case TRUE:
    case FALSE:
      return formula;

    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
    }

  ASSERTION_VIOLATION;
}

FormulaList* SymbolOccurrenceReplacement::process(FormulaList* formulas) {
  CALL("SymbolOccurrenceReplacement::process(FormulaList*)");
  return FormulaList::isEmpty(formulas) ? formulas : new FormulaList(process(formulas->head()), process(formulas->tail()));
}
