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
#include "Kernel/Matcher.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SymbolOccurrenceReplacement.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Term* SymbolOccurrenceReplacement::process(Term* term) {
  ASS(!term->isSort());

  if (term->isSpecial()) {
    Term::SpecialTermData* sd = term->getSpecialData();
    switch (term->specialFunctor()) {
      case SpecialFunctor::ITE:
        return Term::createITE(process(sd->getITECondition()), process(*term->nthArgument(0)), process(*term->nthArgument(1)), sd->getSort());

      case SpecialFunctor::LET:
          return Term::createLet(process(sd->getLetBinding()), process(*term->nthArgument(0)), sd->getSort());

      case SpecialFunctor::FORMULA:
          return Term::createFormula(process(sd->getFormula()));

      case SpecialFunctor::LAMBDA:
        NOT_IMPLEMENTED;
      case SpecialFunctor::MATCH: {
        DArray<TermList> terms(term->arity());
        for (unsigned i = 0; i < term->arity(); i++) {
          terms[i] = process(*term->nthArgument(i));
        }
        return Term::createMatch(sd->getSort(), sd->getMatchedSort(), term->arity(), terms.begin());
      }
    }
    ASSERTION_VIOLATION;
  }

  if (!_isPredicate && (term->functor() == _oldApplication->functor())) {
    Substitution substitution;
    for (unsigned i = 0; i < term->arity(); i++) {
      ALWAYS(MatchingUtils::matchTerms(*_oldApplication->nthArgument(i), process(*term->nthArgument(i)), substitution));
    }
    return SubstHelper::apply(_freshApplication, substitution);
  }

  TermStack arguments;
  for (const auto& arg : anyArgIter(term)) {
    if(arg.isVar() || arg.term()->isSort()){
      arguments.push(arg);
    } else {
      arguments.push(process(arg));        
    }
  }
  return Term::create(term, arguments.begin());
}

TermList SymbolOccurrenceReplacement::process(TermList ts) {
  if (!ts.isTerm()) {
    return ts;
  }

  return TermList(process(ts.term()));
}

Formula* SymbolOccurrenceReplacement::process(Formula* formula) {
  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();

      Literal* processedLiteral;

      if (_isPredicate && (literal->functor() == _oldApplication->functor())) {
        Substitution substitution;
        for (unsigned i = 0; i < literal->arity(); i++) {
          ALWAYS(MatchingUtils::matchTerms(*_oldApplication->nthArgument(i), process(*literal->nthArgument(i)), substitution));
        }

        auto processedLiteral = SubstHelper::apply(static_cast<Literal*>(_freshApplication), substitution);
        if(!literal->polarity()){
          processedLiteral = Literal::complementaryLiteral(processedLiteral);
        }
        return new AtomicFormula(processedLiteral);
      }

      TermStack arguments;
      for (const auto& arg : anyArgIter(literal)) {
        if(arg.isVar() || arg.term()->isSort()){
          arguments.push(arg);
        } else {
          arguments.push(process(arg));
        }
      }
      return new AtomicFormula(Literal::create(literal, arguments.begin()));
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
  return FormulaList::isEmpty(formulas) ? formulas : new FormulaList(process(formulas->head()), process(formulas->tail()));
}
