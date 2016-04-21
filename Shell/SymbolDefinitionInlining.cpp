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
      case Term::SF_FORMULA:
        return TermList(Term::createFormula(process(sd->getFormula())));

      case Term::SF_ITE:
        return TermList(Term::createITE(process(sd->getCondition()),
                                        process(*term->nthArgument(0)),
                                        process(*term->nthArgument(1)),
                                        sd->getSort()));

      case Term::SF_LET:
        return TermList(Term::createLet(sd->getFunctor(), sd->getVariables(),
                                        process(sd->getBinding()),
                                        process(*term->nthArgument(0)),
                                        sd->getSort()));

      case Term::SF_LET_TUPLE:
        return TermList(Term::createTupleLet(sd->getFunctor(), sd->getTupleSymbols(),
                                             process(sd->getBinding()),
                                             process(*term->nthArgument(0)),
                                             sd->getSort()));

      case Term::SF_TUPLE:
        return TermList(Term::createTuple(process(TermList(sd->getTupleTerm())).term()));

      default:
        ASSERTION_VIOLATION_REP(term->toString());;
    }
  }

  Term::Iterator it(term);

  if (!_isPredicate && (term->functor() == _symbol)) {
    return substitute(it);
  }

  Stack<TermList> arguments;
  while (it.hasNext()) {
    arguments.push(process(it.next()));
  }
  return TermList(Term::create(term, arguments.begin()));
}

Formula* SymbolDefinitionInlining::process(Formula* formula) {
  CALL("NewCNF::inlineLetBinding(Formula*)");

  switch (formula->connective()) {
    case LITERAL: {
      Literal* literal = formula->literal();
      Term::Iterator it(literal);

      if (_isPredicate && (literal->functor() == _symbol)) {
        if (literal->polarity()) {
          return BoolTermFormula::create(substitute(it));
        } else {
          return new NegatedFormula(BoolTermFormula::create(substitute(it)));
        }
      }

      Stack<TermList> arguments;
      while (it.hasNext()) {
        arguments.push(process(it.next()));
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

    default:
      ASSERTION_VIOLATION;
  }
}

FormulaList* SymbolDefinitionInlining::process(FormulaList* formulas) {
  CALL("FOOLElimination::SymbolOccurrenceReplacement::process(FormulaList*)");
  // TODO: get rid of recursion here for speed
  return FormulaList::isEmpty(formulas) ? formulas : new FormulaList(process(formulas->head()), process(formulas->tail()));
}