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
#include "Kernel/Matcher.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/SubstHelper.hpp"

#include "SymbolDefinitionInlining.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;
using namespace Shell;

SymbolDefinitionInlining::SymbolDefinitionInlining(Term* lhs, TermList rhs, unsigned freshVarOffset)
  : _isPredicate(lhs->isBoolean()), _lhs(lhs), _rhs(rhs),
    _bound(0), _counter(0), _freshVarOffset(freshVarOffset), _varRenames(0)
{
  // the symbol that we replace must be in the form of a literal
  if (_isPredicate && !_lhs->isLiteral()) {
    ASS(_lhs->isFormula());
    auto inner = _lhs->getSpecialData()->getFormula();
    ASS_EQ(inner->connective(), Connective::LITERAL);
    _lhs = inner->literal();
  }
}

TermList SymbolDefinitionInlining::substitute(Term::Iterator tit)
{
  Substitution substitution;

  for (const auto& baseArg : iterTraits(Term::Iterator(_lhs))) {
    ASS(tit.hasNext());
    // TODO find out if process needs to be called on tit.next() here
    ALWAYS(MatchingUtils::matchTerms(baseArg, tit.next(), substitution));
  }
  ASS(!tit.hasNext());

  if (_counter > 0) {
    /**
     * The _rhs is inlined more than once. In such case, rename it's bound
     * variables.
     */

    if (_counter == 1) {
      /**
       * The second occurrence of the _rhs -- need to calculate it's bound variables.
       *
       * TODO: This is insufficient to cover the case when a variable is bound
       * multiple times in nested expressions. This is left as is for now,
       * because this case cannot occur with let-bindings of constant.
       */
      collectBoundVariables(_rhs);
    }

    for (const auto& boundVar : iterTraits(VList::Iterator(_bound))) {
      unsigned freshVar = ++_freshVarOffset;
      substitution.bindUnbound(boundVar, TermList(freshVar, false));
      List<pair<unsigned, unsigned>>::push(make_pair(boundVar, freshVar), _varRenames);
    }
  }

  _counter++;

  return SubstHelper::apply(_rhs, substitution);
}

TermList SymbolDefinitionInlining::process(TermList ts)
{
  if (ts.isVar() || ts.term()->isSort()) {
    return ts;
  }

  Term* term = ts.term();

  if (term->isSpecial()) {
    Term::SpecialTermData *sd = term->getSpecialData();
    switch (sd->specialFunctor()) {
      case SpecialFunctor::FORMULA: {
        Formula* formula = process(sd->getFormula());

        if (formula == sd->getFormula()) {
          return ts;
        }

        return TermList(Term::createFormula(formula));
      }

      case SpecialFunctor::ITE: {
        Formula* condition  = process(sd->getITECondition());
        TermList thenBranch = process(*term->nthArgument(0));
        TermList elseBranch = process(*term->nthArgument(1));

        if ((condition == sd->getITECondition()) && (thenBranch == *term->nthArgument(0)) && (elseBranch == *term->nthArgument(1))) {
          return ts;
        }

        return TermList(Term::createITE(condition, thenBranch, elseBranch, sd->getSort()));
      }

      case SpecialFunctor::LET: {
        Formula* binding = process(sd->getLetBinding());
        TermList body = process(*term->nthArgument(0));

        if ((sd->getLetBinding() == binding) && (*term->nthArgument(0) == body)) {
          return ts;
        }

        return TermList(Term::createLet(binding, body, sd->getSort()));
      }

      case SpecialFunctor::LAMBDA:
        NOT_IMPLEMENTED;
      case SpecialFunctor::MATCH: {
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

    }
    ASSERTION_VIOLATION_REP(term->toString());
  }

  Term::Iterator terms(term);

  if (!_isPredicate && (term->functor() == _lhs->functor())) {
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

Formula* SymbolDefinitionInlining::process(Formula* formula)
{
  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();
      Term::Iterator terms(literal);

      if (_isPredicate && (literal->functor() == _lhs->functor())) {
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

FormulaList* SymbolDefinitionInlining::process(FormulaList* formulas)
{
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

void SymbolDefinitionInlining::collectBoundVariables(TermList ts)
{
  if (ts.isVar()) {
    return;
  }

  collectBoundVariables(ts.term());
}

void SymbolDefinitionInlining::collectBoundVariables(Term* t)
{
  if (t->shared()) {
    return;
  }

  if (t->isSpecial()) {
    Term::SpecialTermData* sd = t->getSpecialData();
    switch (sd->specialFunctor()) {
      case SpecialFunctor::FORMULA: {
        collectBoundVariables(sd->getFormula());
        break;
      }
      case SpecialFunctor::ITE: {
        collectBoundVariables(sd->getITECondition());
        break;
      }
      case SpecialFunctor::LET: {
        collectBoundVariables(sd->getLetBinding());
        break;
      }
      case SpecialFunctor::LAMBDA:
        NOT_IMPLEMENTED;
      case SpecialFunctor::MATCH: {
        // args are handled below
        break;
      }
    }
  }

  Term::Iterator terms(t);
  while (terms.hasNext()) {
    collectBoundVariables(terms.next());
  }
}

void SymbolDefinitionInlining::collectBoundVariables(Formula* formula) {
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
