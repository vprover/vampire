#include "Kernel/Substitution.hpp"
#include "Kernel/Formula.hpp"

#include "SymbolDefinitionInlining.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

TermList SymbolDefinitionInlining::substitute(Term::Iterator tit) {
  CALL("SymbolDefinitionInlining::constructSubstitution");

  Substitution substitution;

  Formula::VarList::Iterator vit(_bindingVariables);
  while (vit.hasNext()) {
    unsigned var = (unsigned) vit.next();
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

    Formula::VarList::Iterator bit(_bound);
    while (bit.hasNext()) {
      unsigned boundVar = (unsigned) bit.next();
      unsigned freshVar = ++_freshVarOffset;
      substitution.bind(boundVar, TermList(freshVar, false));
      _varRenames = _varRenames->cons(make_pair(boundVar, freshVar));
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

        if (tuple.term() == sd->getTupleTerm()) {
          return ts;
        }

        return TermList(Term::createTuple(tuple.term()));
      }

      default:
        ASSERTION_VIOLATION_REP(term->toString());;
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

Formula* SymbolDefinitionInlining::process(Formula* formula) {
  CALL("NewCNF::inlineLetBinding(Formula*)");

  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();
      Term::Iterator terms(literal);

      if (_isPredicate && (literal->functor() == _symbol)) {
        if (literal->polarity()) {
          return BoolTermFormula::create(substitute(terms));
        } else {
          return new NegatedFormula(BoolTermFormula::create(substitute(terms)));
        }
      }

      bool processed = false;
      Stack<TermList> args;
      while (terms.hasNext()) {
        TermList argument = terms.next();
        TermList flattenedArgument = process(argument);
        if (argument != flattenedArgument) {
          processed = true;
        }
        args.push(flattenedArgument);
      }

      if (!processed) {
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

  static Stack<Formula*> elements;
  elements.reset();

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

  FormulaList* processedFormula = FormulaList::empty();
  Stack<Formula*>::BottomFirstIterator eit(elements);
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
        _bound = Formula::VarList::concat(_bound, sd->getVariables());
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
      _bound = Formula::VarList::concat(_bound, formula->vars());
      collectBoundVariables(formula->qarg());
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