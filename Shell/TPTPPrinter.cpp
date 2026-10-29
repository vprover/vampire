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
 * @file TPTPPrinter.cpp
 * Implements class TPTPPrinter.
 */

#include <sstream>
#include <utility>

#include "Kernel/Connective.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopeGuard.hpp"
#include "Lib/Set.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Parse/TPTP.hpp"
#include "Saturation/Splitter.hpp"

#include "TPTPPrinter.hpp"

#include "Forwards.hpp"

namespace Shell
{

using namespace std;
using TPTPOutput::connectiveSymbol;
using TPTPOutput::disjunction;
using TPTPOutput::InputName;
using TPTPOutput::parenthesized;
using TPTPOutput::Reference;
using TPTPOutput::variableRef;
namespace Language = TPTPOutput::Language;

/**
 * Return the std::string representing the formula f.
 */
std::string TPTPPrinter::toString(const Formula* formula)
{
  std::ostringstream out;
  printFormula(out, formula);
  return out.str();
}

std::ostream& TPTPPrinter::printFormula(std::ostream& out, const Formula* formula)
{
  // render a connective if specified, and then a Formula (or ")" of formula is nullptr)
  typedef pair<Connective,const Formula*> Todo;
  Stack<Todo> stack;
  stack.push(make_pair(NOCONN,formula));
  while (stack.isNonEmpty()) {
    Todo todo = stack.pop();
    // in any case start by rendering the connective passed from "above"
    out << connectiveSymbol(todo.first);
    const Formula* f = todo.second;
    if (!f) {
      out << ")";
      continue;
    }
    Connective c = f->connective();

    switch (c) {
    case LITERAL: {
      if (f->literal()->isEquality()) {
        out << parenthesized(*f->literal());
      } else {
        out << *f->literal();
      }
      continue;
    }
    case AND:
    case OR:
      {
        // we will reverse the order
        // but that should not matter
        const FormulaList* fs = f->args();
        out << "(";
        stack.push(make_pair(NOCONN,nullptr)); // render the final closing bracket
        while (FormulaList::isNonEmpty(fs)) {
          const Formula* arg = fs->head();
          fs = fs->tail();
          // the last argument, which will be printed first, is the only one not preceded by a rendering of con
          stack.push(make_pair(FormulaList::isNonEmpty(fs) ? c : NOCONN,arg));
        }
        continue;
      }
    case IMP:
    case IFF:
    case XOR:
      // here we can afford to keep the order right
      out << "(";
      // render final closing bracket, second argument with con, first argument without con
      stack.pushMany(make_pair(NOCONN,nullptr),make_pair(c,f->right()),make_pair(NOCONN,f->left()));
      continue;

    case NOT:
      out << "(";
      stack.pushMany(make_pair(NOCONN,nullptr), make_pair(c, f->uarg()));
      continue;

    case FORALL:
    case EXISTS:
      {
        out << '(' << connectiveSymbol(c) << '[';
        bool needsComma = false;
        VSList::Iterator vs(f->vars());

        while (vs.hasNext()) {
          auto [var, t] = vs.next();
          if (needsComma) {
            out << ", ";
          }
          out << variableRef(var);
          if (t != AtomicSort::defaultSort()) {
            out << " : " << t;
          }
          needsComma = true;
        }
        out << "] : (";
        stack.pushMany(make_pair(NOCONN,nullptr),make_pair(NOCONN,nullptr),make_pair(NOCONN,f->qarg()));
        continue;
      }
    case BOOL_TERM:
      out << f->getBooleanTerm();
      continue;
    case FALSE:
    case TRUE:
      out << connectiveSymbol(c);
      continue;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return out;
}

/**
 * The universal prefix "![X0 : s,X1 : $i] : " binding, with their sorts, all the
 * variables of @param unit; nothing is written if there are none.
 *
 * Sorts are always spelled out (even the default $i), since making the sorts explicit
 * is the whole point of the prefix. Type variables come first, as they must, and the
 * remaining variables in the order of their numbers, so that the output is stable.
 */
std::ostream& TPTPPrinter::universalPrefix(std::ostream& out, const Unit* unit)
{
  DHMap<unsigned,TermList, FnvHash, IdentityHash> varSorts;
  SortHelper::collectVariableSorts(const_cast<Unit*>(unit), varSorts);
  if (varSorts.isEmpty()) {
    return out;
  }

  Stack<unsigned> vars;
  vars.loadFromIterator(varSorts.domain());
  vars.sort([&varSorts](unsigned v1, unsigned v2) {
    bool t1 = varSorts.get(v1).isTerm() && varSorts.get(v1).term()->isSuper();
    bool t2 = varSorts.get(v2).isTerm() && varSorts.get(v2).term()->isSuper();
    return (t1 != t2) ? t1 : (v1 < v2);
  });

  out << "![";
  out << TPTPOutput::commaSeparated(vars.iter(), [&varSorts](unsigned x) {
    return Lib::Output::deferred([&varSorts, x](std::ostream& out) -> std::ostream& {
      return out << variableRef(x) << " : " << varSorts.get(x);
    });
  });
  return out << "] : ";
}

/**
 * Output unit @param unit in TPTP format as a std::string
 *
 * If the unit is a formula of type @b CONJECTURE, output the
 * negation of Vampire's internal representation with the
 * TPTP role conjecture. If it is a clause, just output it as
 * is, with the role negated_conjecture.
 */
std::string TPTPPrinter::toString(const Unit* unit, bool typedClauses)
{
  std::ostringstream out;
  printUnit(out, unit, typedClauses);
  return out.str();
}

std::ostream& TPTPPrinter::UnitOutput::print(std::ostream& out) const
{ return printUnit(out, unit, typedClauses); }

std::ostream& TPTPPrinter::NamedUnitOutput::print(std::ostream& out) const
{ return printUnit(out, unit, name, role, typedClauses, includeSplitLevels); }

std::ostream& TPTPPrinter::FormulaOutput::print(std::ostream& out) const
{ return printFormula(out, formula); }

std::ostream& TPTPPrinter::printUnit(std::ostream& out, const Unit* unit, bool typedClauses)
{
  auto [role, negateFormula] = TPTPOutput::problemRole(unit);
  out << language(unit, typedClauses) << '(' << InputName{unit, "u"} << ',' << role << ",\n    ";
  printBody(out, unit, typedClauses, negateFormula, /*includeSplitLevels=*/false);
  return out << ").\n";
}

std::ostream& TPTPPrinter::printUnit(std::ostream& out, const Unit* unit, std::string_view name,
    const char* role, bool typedClauses, bool includeSplitLevels)
{
  out << language(unit, typedClauses) << '(' << name << ',' << role << ",\n    ";
  printBody(out, unit, typedClauses, /*negateFormula=*/false, includeSplitLevels);
  return out << ").\n";
}

const char* TPTPPrinter::language(const Unit* unit, bool typedClauses)
{
  if (!unit->isClause()) {
    return Language::TFF;
  }
  if (typedClauses) {
    return Language::TCF;
  }
  return Language::CNF;
}

/**
 * The formula of @param unit. A clause is written in parentheses, preceded by its universal
 * prefix if @param typedClauses. With @param negateFormula, a formula is closed and negated.
 * With @param includeSplitLevels, the split levels of a clause are added as $splitLevel<n>
 * disjuncts; these are a Vampire extension, not TPTP.
 */
std::ostream& TPTPPrinter::printBody(std::ostream& out, const Unit* unit, bool typedClauses,
    bool negateFormula, bool includeSplitLevels)
{
  if (unit->isClause()) {
    const auto* clause = static_cast<const Clause*>(unit);
    if (typedClauses) { universalPrefix(out, unit); }
    out << "( " << disjunction(clause->iterLits());
    if (includeSplitLevels && !clause->noSplits()) {
      for (SplitLevel split : iterTraits(clause->splits()->iter())) {
        out << connectiveSymbol(OR) << Reference{"$splitLevel", split};
      }
    }
    out << " )";
  } else {
    const Formula* formula = static_cast<const FormulaUnit*>(unit)->formula();
    if (!negateFormula) {
      printFormula(out, formula);
    } else {
      Formula* quantified = Formula::quantify(const_cast<Formula*>(formula));
      ScopeGuard cleanup([&] {
        if (quantified != formula) {
          ASS_EQ(quantified->connective(), FORALL);
          VSList::destroy(static_cast<QuantifiedFormula*>(quantified)->vars());
          quantified->destroy();
        }
      });
      if (quantified->connective() == NOT) {
        ASS_EQ(quantified, formula);
        printFormula(out, quantified->uarg());
      } else if (quantified->connective() == LITERAL && quantified->literal()->isNegative()) {
        ASS_EQ(quantified, formula);
        out << *Literal::complementaryLiteral(quantified->literal());
      } else {
        NegatedFormula negated(quantified);
        printFormula(out, &negated);
      }
    }
  }
  return out;
}


namespace TPTPOutput {

QuantifiedVariables::QuantifiedVariables(VirtualIterator<unsigned> variables,
    const DHMap<unsigned, TermList, FnvHash, IdentityHash>& sorts)
{
  while (variables.hasNext()) {
    unsigned number = variables.next();
    Variable variable{number, {}};
    if (auto sort = sorts.find(number)) {
      //a variable of a sort other than $i must always be annotated, and
      //preprocessing is not expected to introduce such a sort into an
      //initially untyped problem. Same predicate as Formula::toString.
      ASS(*sort == AtomicSort::defaultSort() || env.initiallyHasNonDefaultSorts());
      if (env.initiallyHasNonDefaultSorts()) {
        variable.sort = some(*sort);
      }
    }
    if (variable.sort.isSome() && variable.sort->isTerm() && variable.sort->term()->isSuper()) {
      _typeVariables.push(std::move(variable));
    } else {
      _termVariables.push(std::move(variable));
    }
  }
}

std::ostream& operator<<(std::ostream& out, QuantifiedVariables const& self)
{
  // Type variables are bound first; the reversal keeps the established output order.
  out << commaSeparated(self._typeVariables.iter());
  if (self._typeVariables.isNonEmpty() && self._termVariables.isNonEmpty()) {
    out << ',';
  }
  return out << commaSeparated(self._termVariables.iterFifo());
}

std::ostream& operator<<(std::ostream& out, UniversalClosure closure)
{
  Unit* unit = closure.unit;
  DHMap<unsigned, TermList, FnvHash, IdentityHash> sorts;
  SortHelper::collectVariableSorts(unit, sorts, /*ignoreBound=*/true);
  Set<unsigned, FnvHash> variables;

  if (!unit->isClause()) {
    const Formula* formula = static_cast<FormulaUnit*>(unit)->formula();
    variables.insertFromIterator(FormulaVarIterator(formula));
    return out << quantified(QuantifiedVariables(pvi(variables.iter()), sorts),
        formula);
  }

  Clause* clause = unit->asClause();
  for (Literal* literal : clause->iterLits()) {
    variables.insertFromIterator(TermVarIterator(literal)); //TODO update iterator for two var lits?
  }
  return out << quantified(QuantifiedVariables(pvi(variables.iter()), sorts),
      disjunction(clause->iterLits()));
}

const char* connectiveSymbol(Connective connective)
{
  static const char* const symbols[] =
    { "", " & ", " | ", " => ", " <=> ", " <~> ",
      "~ ", "!", "?", "$term", FALSE_CONSTANT, TRUE_CONSTANT, "", ""};
  static_assert(std::size(symbols) == NOCONN + 1, "one symbol per connective");
  return symbols[connective];
}

const char* inputRole(UnitInputType type)
{
  switch (type) {
  case UnitInputType::ASSUMPTION:
    return Role::HYPOTHESIS;
  case UnitInputType::CONJECTURE:
    return Role::CONJECTURE;
  case UnitInputType::NEGATED_CONJECTURE:
    return Role::NEGATED_CONJECTURE;
  case UnitInputType::EXTENSIONALITY_AXIOM:
    return Role::EXTENSIONALITY;
  default:
    return Role::AXIOM;
  }
}

ProblemRole problemRole(const Unit* unit)
{
  switch (unit->conjectureRelation()) {
  case ConjectureRelation::CONJECTURE:
    return {Role::CONJECTURE, false};
  case ConjectureRelation::NEGATED_CONJECTURE:
    return {Role::NEGATED_CONJECTURE, false};
  case ConjectureRelation::NEGATED_FORMULA:
    return {Role::CONJECTURE, true};
  case ConjectureRelation::NONE:
    break;
  }
  return {inputRole(unit->inputType()), false};
}

std::ostream& operator<<(std::ostream& out, SplitLiteral self)
{
  return out << Saturation::Splitter::getFormulaStringFromLiteral(self.literal);
}

std::ostream& operator<<(std::ostream& out, InputName name)
{
  std::string unitName;
  std::filesystem::path unitPath;
  if (Parse::TPTP::findAxiomName(name.unit, unitName, unitPath)) {
    return out << unitName;
  }
  return out << Reference{name.fallbackPrefix, name.unit->number()};
}

} // namespace TPTPOutput

} // namespace Shell
