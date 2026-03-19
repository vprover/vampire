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
 * @file HOLUnificationHandler.cpp
 * Implements class HOLUnificationHandler.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"

#include "HOLUnificationHandler.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)

namespace Saturation {

bool HOLUnificationHandler::isHolUnifiable(TermList t)
{
  return t.isLambdaTerm() || (t.isApplication() && t.head().isVar());
}

bool isHOLUnificationConstraint(Literal* lit)
{
  if (!lit->isEquality() || lit->isPositive() || lit->isFlexFlexConstraint()) {
    return false;
  }
  return HOLUnificationHandler::isHolUnifiable(lit->termArg(0)) || HOLUnificationHandler::isHolUnifiable(lit->termArg(1));
}

HOLUnificationHandler::HOLUnificationHandler(const Options& opt)
: _kNumIter(opt.holUnifierIterations()) { ASS(_kNumIter); }

Clause* HOLUnificationHandler::handleClause(Clause* cl)
{
  ASS(cl->length());
  ASS(cl->numSelected());

  LiteralStack lits;
  auto def_units = UnitList::empty();

  for (unsigned i = 0; i < cl->length(); i++) {
    auto lit = (*cl)[i];

    // only replace selected literals that are HOL unification constraints
    if (i < cl->numSelected() && isHOLUnificationConstraint(lit)) {
      // first unification constraint, push all previous literals
      if (lits.isEmpty()) {
        for (unsigned j = 0; j < i; j++) { lits.push((*cl)[j]); }
      }
      auto [replLit, def] = introduceDefinition(lit);
      lits.push(replLit);
      UnitList::push(def, def_units);
      continue;
    }

    // We started filling the stack, add all literals to it
    if (lits.isNonEmpty()) {
      lits.push(lit);
    }
  }

  if (lits.isNonEmpty()) {
    ASS(def_units);
    UnitList::push(cl, def_units);
    return Clause::fromStack(lits, NonspecificInferenceMany(InferenceRule::HOL_UNIFIER_ELIMINATION, def_units));
  }
  return cl;
}

ClauseStack HOLUnificationHandler::iterate(bool& terminated)
{
  ClauseStack res;

  // do num-many iterations
  for (unsigned j = 0; j < _kNumIter; j++) {

    if (_todo.isEmpty()) {
      break;
    }

    // circulate inside _todos
    if (_index >= _todo.size()) {
      _index = 0;
    }

    auto& curr = _todo[_index];

    LiteralStack solution;
    if (curr.iterate(solution)) {
      DEBUG("finished ", curr);
      _solved.push(_todo.swapRemove(_index));
    } else {
      _index++;
    }

    if (solution.isNonEmpty()) {
      res.push(Clause::fromStack(solution, NonspecificInference0(UnitInputType::AXIOM, InferenceRule::HOL_UNIFIER_SOLUTION)));
    }
  }
  terminated = _todo.isEmpty();
  return res;
}

std::pair<Literal*,Unit*> HOLUnificationHandler::introduceDefinition(Literal* lit)
{
  ASS(isHOLUnificationConstraint(lit));

  Renaming r;
  r.normalizeVariables(lit);
  auto nlit = Literal::complementaryLiteral(r.apply(lit));

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

  // 2. introduce definition if needed

  UCDef* def_ptr;

  if (_litToDefMap.getValuePtr(nlit, def_ptr)) {

    // 2.1. introduce function based on variables

    auto f = env.signature->addFreshFunction(typeVars.size(), "hol_unif");
    auto sym = env.signature->getFunction(f);
    SortHelper::normaliseArgSorts(typeVars, termVarSorts);
    auto srt = AtomicSort::arrowSort(termVarSorts, AtomicSort::boolSort(), /*fromTop=*/true);
    auto type = OperatorType::getConstantsType(srt, typeVars.size());
    sym->setType(type);

    // 2.2. add definition

    auto vl = VSList::empty();
    TermStack typeVarsR;
    for (const auto& v : typeVars) {
      auto vr = r.apply(v);
      VSList::push({ vr.var(), AtomicSort::superSort() }, vl);
      typeVarsR.push(vr);
    }
    TermStack body_args;
    for (const auto& [v,s] : termVars) {
      auto vr = r.apply(v);
      body_args.push(vr);
      VSList::push({ vr.var(), r.apply(s) }, vl);
    }

    TermList head(Term::create(f, typeVarsR.size(), typeVarsR.begin()));
    auto defeq = Literal::createEquality(/*polarity=*/true,
      HOL::create::app(head, body_args, /*fromTop=*/false), TermList(Term::foolTrue()), AtomicSort::boolSort());

    Formula* def = new BinaryFormula(Connective::IFF, new AtomicFormula(defeq), new AtomicFormula(nlit));
    if (vl) {
      def = new QuantifiedFormula(Connective::FORALL, vl, def);
    }
    auto def_u = new FormulaUnit(def, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::HOL_UNIFIER_DEFINITION));

    if (env.options->showAll()) {
      std::cout << "[HOL] introduced definition " << def->toString() << std::endl;
    }

    _todo.emplace(nlit, defeq, r.nextVar());

    *def_ptr = { f, def_u };
  }

  // 3. create new literal

  auto body_s_args = TermStack::fromIterator(iterTraits(termVars.iterFifo()).map([](auto kv){ return kv.first; }));
  TermList head(Term::create(def_ptr->fun, typeVars.size(), typeVars.begin()));
  return { Literal::createEquality(/*polarity=*/false, HOL::create::app(head, body_s_args, /*fromTop=*/false), TermList(Term::foolTrue()), AtomicSort::boolSort()), def_ptr->def };
}

} // namespace Saturation
