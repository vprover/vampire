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
 * @file HOLUnifier.cpp
 * Implements class HOLUnifier.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"

#include "HOLUnifier.hpp"

namespace Saturation {

bool isHOLUnificationConstraint(Literal* lit)
{
  if (!lit->isEquality() || lit->isPositive()) {
    return false;
  }
  return lit->termArg(0).isLambdaTerm() || lit->termArg(1).isLambdaTerm();
}

Clause* HOLUnifier::handleClause(Clause* cl)
{
  ASS(cl->length());

  LiteralStack lits;

  for (unsigned i = 0; i < cl->length(); i++) {
    auto lit = (*cl)[i];

    if (isHOLUnificationConstraint(lit)) {
      for (unsigned j = 0; j < i; j++) { lits.push((*cl)[j]); }
      lits.push(introduceDefinition(lit));
      continue;
    }

    // We started filling the stack, add all literals to it
    if (lits.isNonEmpty()) {
      lits.push(lit);
    }
  }

  if (lits.isNonEmpty()) {
    return Clause::fromStack(lits, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::HOL_UNIFIER_DEFINITION));
  }
  return cl;
}

Literal* HOLUnifier::introduceDefinition(Literal* lit)
{
  ASS(isHOLUnificationConstraint(lit));
  ASS(!lit->ground()); // I think ground cases should be handled elsewhere

  Renaming r;
  r.normalizeVariables(lit);
  auto nlit = r.apply(lit);

  // 1. collect variable sorts
  DHSet<unsigned> varsSeen;
  TermStack typeVars;
  Stack<std::pair<TermList, TermList>> termVars;
  TermStack termVarSorts;

  for (const auto& [v,sort] : iterTraits(VariableWithSortIterator(lit))) {
    if (varsSeen.insert(v.var())) {
      if (sort.isTerm() && sort.term()->isSuper()) {
        typeVars.push(v);
      } else {
        termVars.push({ v, sort });
        termVarSorts.push(sort);
      }
    }
  }

  unsigned* sym_ptr;

  // 2. introduce definition if needed

  if (_defPredMap.getValuePtr(nlit, sym_ptr)) {

    // 2.1. introduce predicate based on variables
    auto p = env.signature->addFreshPredicate(varsSeen.size(), "p_hol");
    auto sym = env.signature->getPredicate(p);
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    auto type = OperatorType::getPredicateType(typeVars.size(), termVarSorts.begin(), termVarSorts.size());
    sym->setType(type);

    // 2.2. add definition

    TermStack p_args;
    auto vl = VList::empty();
    auto sl = SList::empty();
    for (const auto& v : typeVars) {
      auto vr = r.apply(v);
      p_args.push(vr);
      VList::push(vr.var(), vl);
      SList::push(AtomicSort::superSort(), sl);
    }
    for (const auto& [v,s] : termVars) {
      auto vr = r.apply(v);
      auto sr = r.apply(s);
      p_args.push(vr);
      VList::push(vr.var(), vl);
      SList::push(sr, sl);
    }

    auto p_lit = Literal::create(p, /*arity=*/p_args.size(), /*polarity=*/true, p_args.begin());

    auto iff = new BinaryFormula(Connective::IFF, new AtomicFormula(p_lit), new AtomicFormula(nlit));
    auto quantified = new QuantifiedFormula(Connective::FORALL, vl, sl, iff);
    auto def = new FormulaUnit(quantified, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::HOL_UNIFIER_DEFINITION));

    _defs.push(def);
    *sym_ptr = p;
  }

  // 3. create new literal
  auto p_s_args = TermStack::fromIterator(typeVars.iterFifo());
  p_s_args.loadFromIterator(iterTraits(termVars.iterFifo()).map([](auto kv){ return kv.first; }));
  return Literal::create(*sym_ptr, /*arity=*/p_s_args.size(), /*polarity=*/false, p_s_args.begin());
}

} // namespace Saturation
