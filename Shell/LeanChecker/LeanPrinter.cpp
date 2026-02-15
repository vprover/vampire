#include "LeanPrinter.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include <deque>
#include <vector>
#include <algorithm>

namespace Shell {
namespace LeanPrinter {

bool outputBoolOperators = false;

std::ostream &operator<<(std::ostream &out, Escaped escaped)
{
  out << "«_";
  out << escaped.name;
  out << "»";
  return out;
}

std::ostream &operator<<(std::ostream &out, FunctionName name)
{
  auto f = name.symbol;
  if (!f->interpreted())
    return out << Escaped{f->name().c_str()};
  if (f->integerConstant())
    return out << SMTNumeral<false>{f->integerValue()};
  if (f->rationalConstant()) {
    auto rat = f->rationalValue();
    return out << "(" << SMTNumeral<false>{rat.numerator()} << '/' << SMTNumeral<false>{rat.denominator()} << ")";
  }
  if (f->realConstant()) {
    auto rat = f->realValue();
    return out << "(" << SMTNumeral<true>{rat.numerator()} << '/' << SMTNumeral<true>{rat.denominator()} << ")";
  }
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(f);
  switch (interpreted->getInterpretation()) {
    case Theory::EQUAL:
    case Theory::INT_IS_INT:
    case Theory::INT_IS_RAT:
    case Theory::INT_IS_REAL:
    case Theory::INT_GREATER:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_LESS:
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_DIVIDES:
    case Theory::RAT_IS_INT:
    case Theory::RAT_IS_RAT:
    case Theory::RAT_IS_REAL:
    case Theory::RAT_GREATER:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::RAT_LESS:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_IS_INT:
    case Theory::REAL_IS_RAT:
    case Theory::REAL_IS_REAL:
    case Theory::REAL_GREATER:
    case Theory::REAL_GREATER_EQUAL:
    case Theory::REAL_LESS:
    case Theory::REAL_LESS_EQUAL:
      // should be predicates, not functions
      ASSERTION_VIOLATION
    case Theory::INT_SUCCESSOR:
      NOT_IMPLEMENTED;
    case Theory::INT_UNARY_MINUS:
    case Theory::RAT_UNARY_MINUS:
    case Theory::REAL_UNARY_MINUS:
      return out << '-';
    case Theory::INT_PLUS:
    case Theory::RAT_PLUS:
    case Theory::REAL_PLUS:
      return out << '+';
    case Theory::INT_MINUS:
    case Theory::RAT_MINUS:
    case Theory::REAL_MINUS:
      return out << '-';
    case Theory::INT_MULTIPLY:
    case Theory::RAT_MULTIPLY:
    case Theory::REAL_MULTIPLY:
      return out << '*';
    case Theory::INT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT:
    case Theory::REAL_QUOTIENT:
      return out << '/';
    case Theory::INT_QUOTIENT_T:
    case Theory::INT_QUOTIENT_F:
    case Theory::RAT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT_T:
    case Theory::RAT_QUOTIENT_F:
    case Theory::REAL_QUOTIENT_E:
    case Theory::REAL_QUOTIENT_T:
    case Theory::REAL_QUOTIENT_F:
      NOT_IMPLEMENTED;
    case Theory::INT_REMAINDER_E:
      return out << "mod";
    case Theory::INT_REMAINDER_T:
    case Theory::INT_REMAINDER_F:
    case Theory::RAT_REMAINDER_E:
    case Theory::RAT_REMAINDER_T:
    case Theory::RAT_REMAINDER_F:
    case Theory::REAL_REMAINDER_E:
    case Theory::REAL_REMAINDER_T:
    case Theory::REAL_REMAINDER_F:
      NOT_IMPLEMENTED;
    case Theory::INT_TRUNCATE:
    case Theory::RAT_TRUNCATE:
    case Theory::REAL_TRUNCATE:
      NOT_IMPLEMENTED;
    case Theory::INT_ROUND:
    case Theory::RAT_ROUND:
    case Theory::REAL_ROUND:
      NOT_IMPLEMENTED;
    case Theory::INT_ABS:
      NOT_IMPLEMENTED;
    case Theory::RAT_TO_INT:
    case Theory::REAL_TO_INT:
      return out << "to_int";
    case Theory::INT_TO_RAT:
    case Theory::INT_TO_REAL:
      return out << "to_real";
    case Theory::INT_TO_INT:
    case Theory::RAT_TO_RAT:
    case Theory::RAT_TO_REAL:
    case Theory::REAL_TO_RAT:
    case Theory::REAL_TO_REAL:
    case Theory::RAT_FLOOR:
    case Theory::REAL_FLOOR:
    case Theory::RAT_CEILING:
    case Theory::REAL_CEILING:
      ASSERTION_VIOLATION;
    case Theory::INT_FLOOR:
    case Theory::INT_CEILING:
      ASSERTION_VIOLATION;
    case Theory::ARRAY_SELECT:
    case Theory::ARRAY_STORE:
      NOT_IMPLEMENTED;
    case Theory::INVALID_INTERPRETATION:
      ASSERTION_VIOLATION;
  }
  return out;
}

bool isInfix(const Signature::InterpretedSymbol *sym)
{
  switch (sym->getInterpretation()) {
    case Theory::EQUAL:
    case Theory::INT_GREATER:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_LESS:
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_DIVIDES:
    case Theory::RAT_GREATER:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::RAT_LESS:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_GREATER:
    case Theory::REAL_GREATER_EQUAL:
    case Theory::REAL_LESS:
    case Theory::REAL_LESS_EQUAL:
    case Theory::INT_PLUS:
    case Theory::RAT_PLUS:
    case Theory::REAL_PLUS:
    case Theory::INT_MINUS:
    case Theory::RAT_MINUS:
    case Theory::REAL_MINUS:
    case Theory::INT_MULTIPLY:
    case Theory::RAT_MULTIPLY:
    case Theory::REAL_MULTIPLY:
    case Theory::INT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT:
    case Theory::REAL_QUOTIENT:
    case Theory::INT_QUOTIENT_T:
    case Theory::INT_QUOTIENT_F:
    case Theory::RAT_QUOTIENT_E:
    case Theory::RAT_QUOTIENT_T:
    case Theory::RAT_QUOTIENT_F:
    case Theory::REAL_QUOTIENT_E:
    case Theory::REAL_QUOTIENT_T:
    case Theory::REAL_QUOTIENT_F:
    case Theory::INT_REMAINDER_E:
    case Theory::INT_REMAINDER_T:
    case Theory::INT_REMAINDER_F:
    case Theory::RAT_REMAINDER_E:
    case Theory::RAT_REMAINDER_T:
    case Theory::RAT_REMAINDER_F:
    case Theory::REAL_REMAINDER_E:
    case Theory::REAL_REMAINDER_T:
    case Theory::REAL_REMAINDER_F:
      return true;
    default:
      return false;
  }
}

std::ostream &operator<<(std::ostream &out, PredicateName name)
{
  auto p = name.symbol;
  if (!p->interpreted())
    return out << Escaped{p->name().c_str()};
  auto *interpreted = static_cast<Signature::InterpretedSymbol *>(p);
  switch (interpreted->getInterpretation()) {
    case Theory::EQUAL:
      return out << '=';
    case Theory::RAT_IS_INT:
    case Theory::REAL_IS_INT:
      return out << "is_int";
    case Theory::REAL_IS_RAT:
      return out << "is_rat";
    case Theory::INT_GREATER:
    case Theory::RAT_GREATER:
    case Theory::REAL_GREATER:
      return out << '>';
    case Theory::INT_GREATER_EQUAL:
    case Theory::RAT_GREATER_EQUAL:
    case Theory::REAL_GREATER_EQUAL:
      return out << ">=";
    case Theory::INT_LESS:
    case Theory::RAT_LESS:
    case Theory::REAL_LESS:
      return out << '<';
    case Theory::INT_LESS_EQUAL:
    case Theory::RAT_LESS_EQUAL:
    case Theory::REAL_LESS_EQUAL:
      return out << "<=";
    case Theory::INT_DIVIDES:
      NOT_IMPLEMENTED;
    default:
      ASSERTION_VIOLATION;
  }
  return out;
}

std::ostream &operator<<(std::ostream &out, Blank) { return out; }
std::ostream &operator<<(std::ostream &out, Inhabit) { return out << "default"; }

void printArgs(std::ostream &out, Args args, bool variablesAsPattern, bool recurse)
{
  if (args.start->isEmpty())
    return;
  TermList *current = args.start;
  if (current->isVar()) {
    if (variablesAsPattern) {
      out << "_";
      return;
    }
    unsigned var = current->var();
    if (args.conclSorts.findPtr(var)) {
      out << "v" << var;
    }
    else {
      out << "default";
    }
    return;
  }
  bool printed = false;
  if (current->isTerm()) {
    Term *term = current->term();
    FunctionName name(term);
    if (term->arity()) {
      if (name.symbol->interpreted()) {
        auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
        if (isInfix(interpreted) && term->arity() == 2) {
          current = term->termArgs();
          out << "(";
          printArgs(out, Args{current, args.conclSorts, args.otherSorts}, variablesAsPattern, false);
          out << name;
          printArgs(out, Args{current->next(), args.conclSorts, args.otherSorts}, variablesAsPattern, recurse);
          out << ")";
          printed = true;
        }
      }
      else if (name.symbol->linMul()) {
        out << "(";
        if (auto attempt = env.signature->tryLinMul<IntegerConstantType>(term->functor()); attempt.isSome()) {
          auto factor = SMTNumeral<false>{attempt.unwrap()};
          out << factor << "*";
        }
        else if (auto attempt = env.signature->tryLinMul<RationalConstantType>(term->functor()); attempt.isSome()) {
          auto factor = attempt.unwrap();
          out << "( " << SMTNumeral<true>{factor.numerator()} << "/" << SMTNumeral<true>{factor.denominator()} << ")";
        }
        else if (auto attempt = env.signature->tryLinMul<RealConstantType>(term->functor()); attempt.isSome()) {
          auto factor = attempt.unwrap();
          out << "( " << SMTNumeral<true>{factor.numerator()} << "/" << SMTNumeral<true>{factor.denominator()} << ")";
        }
        else
          ASSERTION_VIOLATION
        printArgs(out, Args{term->termArgs(), args.conclSorts, args.otherSorts}, variablesAsPattern, recurse);
        out << ")";
        printed = true;
      }
    }
    if (!printed) {
      if (term->arity()) {
        out << "(" << name;
        current = term->termArgs();
        std::deque<TermList *> todo;
        while (!current->isEmpty()) {
          todo.push_back(current);
          current = current->next();
        }
        while (!(todo.size() == 0)) {
          out << " ";
          printArgs(out, Args{todo.front(), args.conclSorts, args.otherSorts}, variablesAsPattern, false);
          todo.pop_front();
        }
        out << ")";
      }
      else {
        out << name;
      }
    }
  }
}

std::ostream &operator<<(std::ostream &out, Args args)
{
  printArgs(out, args, false, true);
  return out;
}

void printLiteral(std::ostream &out, Lit lit, bool variablesAsPattern)
{
  Literal *literal = lit.literal;
  PredicateName name(literal);
  if (!literal->polarity())
    out << "(¬";
  if (literal->arity())
    out << "(";
  if (name.symbol->interpreted()) {
    auto interpreted = static_cast<Signature::InterpretedSymbol *>(name.symbol);
    switch (interpreted->getInterpretation()) {
      case Theory::INT_IS_INT:
      case Theory::INT_IS_RAT:
      case Theory::INT_IS_REAL:
      case Theory::RAT_IS_RAT:
      case Theory::RAT_IS_REAL:
      case Theory::REAL_IS_REAL:
        out << "True";
      default:
        break;
    }
    if (isInfix(interpreted) && literal->arity() == 2) {
      TermList *current = literal->args();
      printArgs(out, Args{current, lit.conclSorts, lit.otherSorts}, variablesAsPattern, true);
      out << name;
      printArgs(out, Args{current->next(), lit.conclSorts, lit.otherSorts}, variablesAsPattern, true);
    }
    else {
      out << name;
      auto args = literal->args();
      while (args->isNonEmpty()) {
        out << " ";
        printArgs(out, Args{args, lit.conclSorts, lit.otherSorts}, variablesAsPattern, true);
        args = args->next();
      }
    }
  }
  else {
    out << name;
    auto args = literal->args();
    while (args->isNonEmpty()) {
      out << " ";
      printArgs(out, Args{args, lit.conclSorts, lit.otherSorts}, variablesAsPattern, true);
      args = args->next();
    }
  }
  if (literal->arity())
    out << ")";
  if (!literal->polarity())
    out << ")";
}

std::ostream &operator<<(std::ostream &out, Lit lit)
{
  printLiteral(out, lit);
  return out;
}

std::ostream &operator<<(std::ostream &out, Sort print)
{
  AtomicSort *sort = static_cast<AtomicSort *>(print.sort.term());
  ASS_EQ(sort->arity(), 0)
  return out << SortName(sort);
}

void outputSortsWithQuantor(std::ostream &out, SortMap &sorts, std::string quantor, std::string end)
{
  if (sorts.isEmpty())
    return;
  auto it = sorts.items();
  std::vector<std::pair<unsigned, TermList>> vars;
  while (it.hasNext()) {
    auto [var, sort] = it.next();
    vars.push_back(std::make_pair(var, sort));
  }

  std::sort(vars.begin(), vars.end(), [](std::pair<unsigned, TermList> a, std::pair<unsigned, TermList> b) { return a.first < b.first; });

  TermList previous = vars.begin()->second;
  bool first = true;

  for (auto [var, sort] : vars) {
    if (first) {
      out << quantor;
    }
    if (sort != previous) {
      out << " : " << Sort{previous} << end << quantor;
    }
    out << " v" << var;
    first = false;
    previous = sort;
  }
  out << " : " << Sort{previous} << end;
}

void printFormula(std::ostream &out, Formula *f, SortMap &conclSorts, SortMap &otherSorts, bool variablesAsPattern)
{
  switch (f->connective()) {
    case LITERAL:
      printLiteral(out, Lit{f->literal(), conclSorts, otherSorts}, variablesAsPattern);
      break;
    case AND: {
      out << "(";
      Kernel::FormulaList *reversedList = FormulaList::reverse(FormulaList::copy(f->args()));
      auto args = reversedList->iter();
      while (args.hasNext()) {
        printFormula(out, args.next(), conclSorts, otherSorts, variablesAsPattern);
        if (args.hasNext()){
          if(outputBoolOperators){
            out << " && ";
          } else {
            out << " ∧ ";
          }
        }
      }
      FormulaList::destroy(reversedList);
      out << ")";
    } break;
    case OR: {
      out << "( ";
      auto reversedList = FormulaList::reverse(FormulaList::copy(f->args()));
      auto args = reversedList->iter();
      while (args.hasNext()) {
        printFormula(out, args.next(), conclSorts, otherSorts, variablesAsPattern);
        if (args.hasNext()){
          if(outputBoolOperators){
            out << " || ";
          } else {
            out << " ∨ ";
          }
        }
      }
      FormulaList::destroy(reversedList);
      out << ")";
    } break;
    case IMP:
      out << "(";
      printFormula(out, f->left(), conclSorts, otherSorts, variablesAsPattern);
      out << " → ";
      printFormula(out, f->right(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
      break;
    case IFF:
      out << "(";
      printFormula(out, f->left(), conclSorts, otherSorts, variablesAsPattern);
      out << " ↔ ";
      printFormula(out, f->right(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
      break;
    case XOR:
      out << "(Xor' ";
      printFormula(out, f->left(), conclSorts, otherSorts, variablesAsPattern);
      out << " ";
      printFormula(out, f->right(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
      break;
    case NOT:
      out << "(¬";
      printFormula(out, f->uarg(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
      break;
    case FORALL: {
      VList::Iterator vs(f->vars());
      SortMap map;
      while (vs.hasNext()) {
        auto var = vs.next();
        map.insert(var, otherSorts.get(var));
      }
      out << "(";
      outputSortsWithQuantor(out, map, "∀");
      printFormula(out, f->qarg(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
    } break;
    case EXISTS: {
      VList::Iterator vs(f->vars());
      SortMap map;
      while (vs.hasNext()) {
        auto var = vs.next();
        map.insert(var, otherSorts.get(var));
      }
      out << "(";
      outputSortsWithQuantor(out, map, "∃");
      printFormula(out, f->qarg(), conclSorts, otherSorts, variablesAsPattern);
      out << ")";
    } break;
    case BOOL_TERM:
      out << "missing bool term implementation for Lean output" << std::endl;
      ASSERTION_VIOLATION;
      break;
    case TRUE:
      out << "True";
      break;
    case FALSE:
      out << "False";
      break;
    case NAME:
      out << (static_cast<NamedFormula*>(f)->name()).c_str();
      break;
    default:
      ASSERTION_VIOLATION;
  }
}

} // namespace LeanPrinter
} // namespace Shell
