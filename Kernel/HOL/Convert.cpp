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
 * @file Convert.cpp
 */

#include <unordered_map>

#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/HOL/HOL.hpp"

using IndexSortPair = std::pair<int, TermList>;
using VarToIndexMap = std::unordered_map<unsigned, IndexSortPair>;

static TermList sortOf(TermList t) {
  ASS(t.isTerm())

  return SortHelper::getResultSort(t.term());
}

static TermList termToNameless(TermList term, const VarToIndexMap& map);
static TermList formulaToNameless(Formula *formula, const VarToIndexMap& map);

static TermList toNamelessAux(VList* vars, SList* sorts, TermList body, TermList bodySort, const VarToIndexMap& map) {
  VarToIndexMap newMap;
  for (const auto& [key, val] : map) {
    newMap.insert({key, {val.first + 1, val.second}});
  }
  newMap[vars->head()] = {0, sorts->head()};

  const auto converted =
    vars->tail() == nullptr ? termToNameless(body, newMap)
                            : toNamelessAux(vars->tail(), sorts->tail(), body, bodySort, newMap);

  bodySort = converted.isVar() ? bodySort : sortOf(converted);
  return HOL::create::namelessLambda(sorts->head(), bodySort, converted);
}



static TermList termToNameless(TermList term, const VarToIndexMap& map) {
  if (term.isVar()) {
    if (const auto p = map.find(term.var()); p != map.end()) {
      const auto& [index, sort] = p->second;
      return HOL::getDeBruijnIndex(index, sort);
    }

    return term;
  }

  const auto t = term.term();
  if (t->isSpecial()) {
    switch (t->specialFunctor()) {
      case SpecialFunctor::FORMULA:
        return formulaToNameless(t->getSpecialData()->getFormula(), map);

      case SpecialFunctor::LAMBDA: {
        const auto sd = t->getSpecialData();
        const auto sorts = sd->getLambdaVarSorts();
        const auto vars = sd->getLambdaVars();

        const auto eliminated = toNamelessAux(vars, sorts, sd->getLambdaExp(), sd->getLambdaExpSort(), map);
        ASS_REP2(eliminated.isVar() || sortOf(eliminated) == sd->getSort(), t->toString(), eliminated.toString())
        return eliminated;
      }

      default:
        ASSERTION_VIOLATION;
    }
  }

  if (!t->isApplication())
    return term;

  //must be of the form app(s1, s2, arg1, arg2)
  auto s1 = *t->nthArgument(0);
  auto s2 = *t->nthArgument(1);
  auto arg1 = *t->nthArgument(2);
  auto arg2 = *t->nthArgument(3);

  return HOL::create::app(s1, s2, termToNameless(arg1, map), termToNameless(arg2, map));
}

static constexpr const char* connectiveToString(Connective conn) {
  switch (conn) {
    case Connective::IFF: return "vIFF";
    case Connective::IMP: return "vIMP";
    case Connective::XOR: return "vXOR";
    case Connective::AND: return "vAND";
    case Connective::OR: return  "vOR";
    default: return "";
  }
}

static TermList formulaToNameless(Formula *formula, const VarToIndexMap& map) {
  switch (const auto conn = formula->connective()) {
    case Connective::LITERAL: {
      const Literal *lit = formula->literal();
      ASS(lit->isEquality()) // Is this a valid assumption?

      auto lhs = termToNameless(*lit->nthArgument(0), map);
      auto rhs = termToNameless(*lit->nthArgument(1), map);
      auto equalsSort = SortHelper::getEqualityArgumentSort(lit);
      auto appTerm = HOL::create::app2(HOL::create::equality(equalsSort), lhs, rhs);

      return lit->polarity() ? appTerm : HOL::create::app(HOL::create::neg(), appTerm);
    }
    case Connective::IFF:
    case Connective::IMP:
    case Connective::XOR: {
      auto *lhs = formula->left();
      auto *rhs = formula->right();

      auto constant = TermList(Term::createConstant(env.signature->getBinaryProxy(connectiveToString(conn))));
      const auto form1 = formulaToNameless(lhs, map);
      const auto form2 = formulaToNameless(rhs, map);

      return HOL::create::app2(constant, form1, form2);
    }
    case Connective::AND:
    case Connective::OR: {
      FormulaList::Iterator argsIt(formula->args());

      auto constant = TermList(Term::createConstant(env.signature->getBinaryProxy(connectiveToString(conn))));

      TermList appTerm;
      for (unsigned count = 1; argsIt.hasNext(); ++count) {
        auto *arg = argsIt.next();
        const auto form = formulaToNameless(arg, map);
        appTerm = count == 1 ? HOL::create::app(constant, form) :
                  count == 2 ? HOL::create::app(appTerm,  form) :
                               HOL::create::app2(constant, appTerm, form);
      }

      return appTerm;
    }

    case Connective::NOT:
      return HOL::create::app(HOL::create::neg(),
                              formulaToNameless(formula->uarg(), map));

    case Connective::FORALL:
    case Connective::EXISTS: {
      Kernel::VList::Iterator vit(formula->vars());
      auto form = TermList(Term::createFormula(formula->qarg()));

      TermList s;
      while (vit.hasNext()) {
        const auto v = vit.next();
        ALWAYS(Kernel::SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        if (s == AtomicSort::superSort()) {
          USER_ERROR("Vampire does not support full TH1. This benchmark is either outside of the TH1 fragment, or outside of the fragment supported by Vampire");
        }
        const auto var = VList::singleton(v);
        const auto sort = SList::singleton(s);
        const auto t = TermList(Term::createLambda(form, var, sort, AtomicSort::boolSort()));
        form = HOL::create::app(conn == Connective::FORALL ? HOL::create::pi(s)
                                                           : HOL::create::sigma(s), t);
      }
      return termToNameless(form, map);
    }
    case Connective::BOOL_TERM:
      return termToNameless(formula->getBooleanTerm(), map);
    case Connective::TRUE:
      return TermList(Term::foolTrue());
    case Connective::FALSE:
      return TermList(Term::foolFalse());
    default:
      ASSERTION_VIOLATION;
  }
}

TermList HOL::convert::toNameless(TermList term) {
  return termToNameless(term, {});
}
