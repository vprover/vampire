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

#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/HOL/HOL.hpp"

using Kernel::Term;

using IndexSortPair = std::pair<int,TermList>;
using VarToIndexMap = std::unordered_map<unsigned, IndexSortPair>;

static TermList sortOf(TermList t) {
  ASS(t.isTerm())

  return Kernel::SortHelper::getResultSort(t.term());
}

static TermList toNameless(TermList term, VarToIndexMap& map);

static TermList toNameless(Kernel::VList* vars, Kernel::SList* sorts, TermList body, TermList bodySort, VarToIndexMap& map) {
  VarToIndexMap newMap;
  for (const auto& [key, val] : map) {
    newMap.insert({key, {val.first + 1, val.second}});
  }
  ASS(newMap.insert({vars->head(), {0, sorts->head()}}).second)

  const auto converted =
    vars->tail() == nullptr ? toNameless(body, newMap) :
                              toNameless(vars->tail(), sorts->tail(), body, bodySort, newMap);

  bodySort = converted.isVar() ? bodySort : sortOf(converted);
  return HOL::create::namelessLambda(sorts->head(), bodySort, converted);
}

static TermList toNameless(Kernel::Formula *formula, VarToIndexMap &map);

static TermList toNameless(TermList term, VarToIndexMap& map) {
  if (term.isVar()) {
    if (auto p = map.find(term.var(), p); p != map.end())
      return HOL::getDeBruijnIndex(p->first, p->second);

    return term;
  }

  auto t = term.term();
  if (t->isSpecial()) {
    switch (t->specialFunctor()) {
      case Kernel::SpecialFunctor::FORMULA:
        return toNameless(t->getSpecialData()->getFormula(), map);

      case Kernel::SpecialFunctor::LAMBDA: {
        auto sd = t->getSpecialData();
        auto sorts = sd->getLambdaVarSorts();
        auto vars = sd->getLambdaVars();

        auto eliminated = toNameless(vars, sorts, sd->getLambdaExp(), sd->getLambdaExpSort(), map);
        ASS_REP2(eliminated.isVar() || sortOf(eliminated) == sd->getSort(), t->toString(), eliminated.toString())
        return eliminated;
      }

      default:
        ASSERTION_VIOLATION;
    }
  }

  if (!t->isApplication()) {
    return term;
  }

  //must be of the form app(s1, s2, arg1, arg2)
  auto s1 = *t->nthArgument(0);
  auto s2 = *t->nthArgument(1);
  auto arg1 = *t->nthArgument(2);
  auto arg2 = *t->nthArgument(3);

  return HOL::create::app(s1, s2, toNameless(arg1, map), toNameless(arg2, map));
}

static TermList toNameless(Kernel::Formula *formula, VarToIndexMap &map) {
  using Kernel::Connective;

  Connective conn = formula->connective();

  switch (conn) {
    case Connective::LITERAL: {
      Kernel::Literal *lit = formula->literal();
      ASS(lit->isEquality()) // Is this a valid assumption?

      auto lhs = toNameless(*lit->nthArgument(0), map);
      auto rhs = toNameless(*lit->nthArgument(1), map);
      auto equalsSort = Kernel::SortHelper::getEqualityArgumentSort(lit);
      auto appTerm = HOL::create::app2(HOL::create::equality(equalsSort), lhs, rhs);

      return lit->polarity() ? appTerm : HOL::create::app(HOL::create::neg(), appTerm);
    }
    case Connective::IFF:
    case Connective::IMP:
    case Connective::XOR: {
      auto *lhs = formula->left();
      auto *rhs = formula->right();

      std::string name =
          conn == Connective::IFF ? "vIFF" :
          conn == Connective::IMP ? "vIMP" :
                                    "vXOR";

      auto constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));
      const auto form1 = toNameless(lhs, map);
      const auto form2 = toNameless(rhs, map);

      return HOL::create::app2(constant, form1, form2);
    }
    case Connective::AND:
    case Connective::OR: {
      Kernel::FormulaList::Iterator argsIt(formula->args());

      const std::string name = conn == Connective::AND ? "vAND" : "vOR";
      auto constant = TermList(Term::createConstant(env.signature->getBinaryProxy(name)));

      TermList appTerm;
      unsigned count = 1;

      while (argsIt.hasNext()) {
        auto *arg = argsIt.next();
        const auto form = toNameless(arg, map);
        appTerm = count == 1 ? HOL::create::app(constant, form) :
                  count == 2 ? HOL::create::app(appTerm,  form) :
                               HOL::create::app2(constant, appTerm, form);

        count++;
      }
      return appTerm;
    }
    case Connective::NOT: {
      TermList form = toNameless(formula->uarg(), map);
      return HOL::create::app(HOL::create::neg(), form);
    }
    case Connective::FORALL:
    case Connective::EXISTS: {
      const auto *vars = formula->vars();
      Kernel::VList::Iterator vit(vars);
      auto form = TermList(Term::createFormula(formula->qarg()));

      TermList s;
      while (vit.hasNext()) {
        const auto v = vit.next();
        ALWAYS(Kernel::SortHelper::tryGetVariableSort(v, formula->qarg(), s));
        if (s == Kernel::AtomicSort::superSort()) {
          USER_ERROR("Vampire does not support full TH1. This benchmark is either outside of the TH1 fragment, or outside of the fragment supported by Vampire");
        }
        auto var = Kernel::VList::singleton(v);
        auto sort = Kernel::SList::singleton(s);
        auto t = TermList(Term::createLambda(form, var, sort, Kernel::AtomicSort::boolSort()));
        form = HOL::create::app(conn == Connective::FORALL ? HOL::create::pi(s) :
                                                             HOL::create::sigma(s), t);
      }
      return toNameless(form, map);
    }
    case Connective::BOOL_TERM:
      return toNameless(formula->getBooleanTerm(), map);
    case Connective::TRUE:
      return TermList(Term::foolTrue());
    case Connective::FALSE:
      return TermList(Term::foolFalse());
    default:
      ASSERTION_VIOLATION;
  }
}

TermList HOL::convert::toNameless(Term* term) {
  return toNameless(TermList(term));
}

TermList HOL::convert::toNameless(TermList term) {
  VarToIndexMap map;
  return ::toNameless(term, map);
}