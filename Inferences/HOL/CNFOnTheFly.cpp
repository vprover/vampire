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
 * @file CNFOnTheFly.cpp
 * Defines classes for clausification on the fly.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/SortHelper.hpp"

#include "Shell/Skolem.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "CNFOnTheFly.hpp"

namespace Inferences {
using namespace std;
using namespace Indexing;

static Clause* replaceLits(Clause* c, Literal* what, Proxy p, bool incAge, Literal* by1, Literal* by2 = nullptr);
static TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt);
static TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt);
static InferenceRule convert(Proxy cnst);
static ClauseIterator produceClauses(Clause* c, bool generating, SkolemisingFormulaIndex* index = 0);

Literal* boolEq(TermList lhs, TermList rhs) {
  return Literal::createEquality(true, lhs, rhs, AtomicSort::boolSort());
}
Literal* eqTroo(TermList lhs) { return boolEq(lhs, HOL::create::top()); }
Literal* eqFols(TermList lhs) { return boolEq(lhs, HOL::create::bottom()); }

ClauseIterator produceClauses(Clause* c, bool generating, SkolemisingFormulaIndex* index)
{
  static bool eager = env.options->cnfOnTheFly() == Options::CNFOnTheFly::EAGER;
  static bool instantiations = env.options->cnfOnTheFly() == Options::CNFOnTheFly::CONJ_EAGER;
  static bool simp = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP || instantiations;
  static bool gen = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_GEN;
  static bool simp_except_not_be_off = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP_NOT_GEN_BOOL_EQ_OFF;
  static bool simp_except_not_and_be = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP_NOT_GEN_BOOL_EQ_GEN;
  static bool simp_except_pi_sigma_gen = env.options->cnfOnTheFly() == Options::CNFOnTheFly::LAZY_SIMP_PI_SIGMA_GEN;
  // if we don't want to simplify <=>, or we want to simplify it as a generating inference, but we have reached here
  // from a simplification inference, or the opposite
  bool not_be = simp_except_not_be_off || (!generating && simp_except_not_and_be) ||
                                          ( generating && simp_except_pi_sigma_gen);

  if(generating && (eager || simp)){ return ClauseIterator::getEmpty(); }
  if(!generating && gen){ return ClauseIterator::getEmpty(); }

  if (instantiations) {
    INVALID_OPERATION("Options::CNFOnTheFly::CONJ_EAGER not yet supported");
  }

  static TermStack args;

  for (const auto& lit : *c) {
    auto [lhs, rhs] = lit->eqArgs();

    TermList term;
    TermList boolVal;
    if (HOL::isBool(lhs)) {
      boolVal = lhs;
      term = rhs;
    } else if (HOL::isBool(rhs)) {
      boolVal = rhs;
      term = lhs;
    } else if (SortHelper::getEqualityArgumentSort(lit) == AtomicSort::boolSort() && !not_be) {
      //equality or diseqality between boolean terms
      if (lit->isPositive()) {
        return pvi(iterItems(
          replaceLits(c, lit, Proxy::IFF, true, eqTroo(lhs), eqFols(rhs)),
          replaceLits(c, lit, Proxy::IFF, true, eqFols(lhs), eqTroo(rhs))
        ));
      }
      return pvi(iterItems(
        replaceLits(c, lit, Proxy::XOR, true, eqTroo(lhs), eqTroo(rhs)),
        replaceLits(c, lit, Proxy::XOR, true, eqFols(lhs), eqFols(rhs))
      ));
    } else {
      continue;
    }

    auto head = HOL::getHeadAndArgs(term, args);
    if (head.isVar()) {
      continue;
    }

    Proxy prox = env.signature->getFunction(head.term()->functor())->proxy();
    // need to decide whether to continue at this point or not
    if(simp_except_pi_sigma_gen){
      if(generating && prox != Proxy::PI && prox != Proxy::SIGMA){
        continue;
      }
      if(!generating && (prox == Proxy::PI || prox == Proxy::SIGMA)){
        continue;
      }
    }
    if(simp_except_not_be_off || simp_except_not_and_be){
      if(generating && prox != Proxy::NOT){
        continue;
      }
      if(!generating && prox == Proxy::NOT){
        continue;
      }
    }

    // Note: at this point we know that one equality argument is either
    // troo or fols, so the other side must be a fully applied proxy,
    // hence assertions about the size of args below suffices.
  
    bool positive = HOL::isTrue(boolVal) == lit->polarity();
    switch (prox) {
      case Proxy::NOT_PROXY:
      case Proxy::IFF:
      case Proxy::XOR: {
        // iff and xor are dealt with by IFFXORRewriter
        break;
      }
      case Proxy::OR: {
        ASS_EQ(args.size(),2);
        if(positive){
          return pvi(iterItems(replaceLits(c, lit, prox, false,
            eqTroo(args[0]), eqTroo(args[1]))));
        }
        return pvi(iterItems(
          replaceLits(c, lit, prox, true, eqFols(args[0])),
          replaceLits(c, lit, prox, true, eqFols(args[1]))
        ));
      }
      case Proxy::AND: {
        ASS_EQ(args.size(),2);
        if(positive){
          return pvi(iterItems(
            replaceLits(c, lit, prox, true, eqTroo(args[0])),
            replaceLits(c, lit, prox, true, eqTroo(args[1]))
          ));
        }
        return pvi(iterItems(replaceLits(c, lit, prox, false,
          eqFols(args[0]), eqFols(args[1]))));
      }
      case Proxy::IMP: {
        ASS_EQ(args.size(),2);
        if(positive){
          return pvi(iterItems(replaceLits(c, lit, prox, false,
            eqFols(args[1]), eqTroo(args[0]))));
        }
        return pvi(iterItems(
          replaceLits(c, lit, prox, true, eqFols(args[0])),
          replaceLits(c, lit, prox, true, eqTroo(args[1]))
        ));
      }
      case Proxy::EQUALS: {
        ASS_EQ(args.size(), 2);
        TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
        return pvi(iterItems(replaceLits(c, lit, prox, false,
          Literal::createEquality(positive, args[0], args[1], srt))));
      }
      case Proxy::NOT: {
        ASS_EQ(args.size(), 1);
        return pvi(iterItems(replaceLits(c, lit, prox, false,
          positive ? eqFols(args[0]) : eqTroo(args[0]))));
      }
      case Proxy::PI:
      case Proxy::SIGMA: {
        ASS_EQ(args.size(), 1);
        TermList srt = *SortHelper::getResultSort(head.term()).term()->nthArgument(0);
        TermList newTerm;
        Proxy proxy;
        if((prox == Proxy::PI && positive) ||
          (prox == Proxy::SIGMA && !positive)){
          proxy = Proxy::PI;
          newTerm = piRemoval(args[0], c, srt);
        } else {
          ASS(term.isTerm());
          bool newTermCreated = false;
          if(index){
            auto results = index->getGeneralizations(TypedTermList(term.term()), true);
            if(results.hasNext()){
              auto tqr = results.next();
              TermList skolemTerm = tqr.data->value;
              skolemTerm = tqr.unifier->applyToBoundResult(skolemTerm);
              newTerm = HOL::create::app(srt, args[0], skolemTerm);
              newTermCreated = true;
            }
          }
          if(!newTermCreated){
            TermList skolemTerm = sigmaRemoval(args[0], srt);
            if(index){
              index->insertFormula(TypedTermList(term.term()), skolemTerm);
            }
            newTerm = HOL::create::app(srt, args[0], skolemTerm);
          }
          proxy = Proxy::SIGMA;
        }
        return pvi(iterItems(replaceLits(c, lit, proxy, false,
          positive ? eqTroo(newTerm) : eqFols(newTerm))));
      }
    }
  }
  return ClauseIterator::getEmpty();
}

Clause* replaceLits(Clause* c, Literal* what, Proxy p, bool incAge, Literal* by1, Literal* by2)
{
  RStack<Literal*> lits;

  for (const auto& lit : *c) {
    lits->push(lit == what ? by1 : lit);
  }
  // adding new literals at different places...
  if (by2) { lits->push(by2); }

  auto out = Clause::fromStack(*lits, NonspecificInference1(convert(p), c));
  // Can be either generating or simplifying. Therefore use NonspecificInference
  // Age is updated in some instances, but not in others based on empirical evaluation
  out->setAge(incAge? c->age() + 1 : c->age());
  return out;
}

InferenceRule convert(Proxy cnst) {
  switch(cnst){
    case Proxy::PI:
      return InferenceRule::PI_PROXY_CLAUSIFICATION;
    case Proxy::SIGMA:
      return InferenceRule::SIGMA_PROXY_CLAUSIFICATION;
    case Proxy::EQUALS:
      return InferenceRule::EQUALITY_PROXY_CLAUSIFICATION;
    case Proxy::NOT:
      return InferenceRule::NOT_PROXY_CLAUSIFICATION;
    case Proxy::AND:
      return InferenceRule::AND_PROXY_CLAUSIFICATION;
    case Proxy::OR:
      return InferenceRule::OR_PROXY_CLAUSIFICATION;
    case Proxy::IMP:
      return InferenceRule::IMP_PROXY_CLAUSIFICATION;
    case Proxy::IFF:
      return InferenceRule::IFF_PROXY_CLAUSIFICATION;
    case Proxy::XOR:
      return InferenceRule::XOR_PROXY_CLAUSIFICATION;
    default:
      ASSERTION_VIOLATION;
  }
}

TermList sigmaRemoval(TermList sigmaTerm, TermList expsrt){
  static DHMap<unsigned,TermList> varSorts;
  varSorts.reset();

  if(sigmaTerm.isTerm()){
    for (const auto& [var, sort] : iterTraits(VariableWithSortIterator(sigmaTerm.term()))) {
      varSorts.insert(var.var(), sort);
    }
  } else {
    varSorts.insert(sigmaTerm.var(), expsrt);
    if(expsrt.isTerm()){
      for (const auto& [var, sort] : iterTraits(VariableWithSortIterator(expsrt.term()))) {
        varSorts.insert(var.var(), sort);
      }
    } else {
      varSorts.insert(expsrt.var(), AtomicSort::superSort());
    }
  }

  static TermStack termVarSorts;
  static TermStack termVars;
  static TermStack typeVars;
  termVarSorts.reset();
  termVars.reset();
  typeVars.reset();

  unsigned var;
  TermList varSort;
  DHMap<unsigned, TermList>::Iterator mapIt(varSorts);
  while(mapIt.hasNext()) {
    mapIt.next(var, varSort);
    if(varSort == AtomicSort::superSort()){
      typeVars.push(TermList(var, false));
    } else {
      termVarSorts.push(varSort);
      termVars.push(TermList(var, false));
    }
  }

  TermList resultSort = *expsrt.term()->nthArgument(0);

  SortHelper::normaliseArgSorts(typeVars, termVarSorts);
  SortHelper::normaliseSort(typeVars, resultSort);

  // TODO Double check this arrow sort, as the order changed. By the looks of it, it was also wrong here.
  TermList skSymSort = AtomicSort::arrowSort(termVarSorts, resultSort);
  unsigned fun = Skolem::addSkolemFunction(typeVars.size(), typeVars.size(), 0, skSymSort);
  TermList head = TermList(Term::create(fun, typeVars.size(), typeVars.begin()));
  TermList skolemTerm = HOL::create::app(head, termVars);

  ASS(*expsrt.term()->nthArgument(1) == AtomicSort::boolSort());
  //cout << "OUT OF sigmaRemoval " + sigmaTerm.toString() << endl;

  return skolemTerm;
}

TermList piRemoval(TermList piTerm, Clause* clause, TermList expsrt){

  unsigned maxVar = clause->maxVar();
  do {
    maxVar++;
    piTerm = HOL::create::app(expsrt, piTerm, TermList::var(maxVar));
    expsrt = *expsrt.term()->nthArgument(1);
  } while(expsrt != AtomicSort::boolSort());

  return piTerm;
}

Clause* IFFXORRewriterISE::simplify(Clause* c){
  TermList boolSort = AtomicSort::boolSort();

  static TermStack args;

  for (const auto& lit : *c) {
    auto [lhs, rhs] = lit->eqArgs();
    TermList term;
    TermList boolVal;
    if(HOL::isBool(lhs)){
      boolVal = lhs;
      term = rhs;
    } else if(HOL::isBool(rhs)){
      boolVal = rhs;
      term = lhs;
    } else {
      continue;
    }

    bool positive = HOL::isTrue(boolVal) == lit->polarity();

    auto head = HOL::getHeadAndArgs(term, args);
    if (head.isVar()) {
      continue;
    }
    auto prox = env.signature->getFunction(head.term()->functor())->proxy();

    if (prox == Proxy::IFF || prox == Proxy::XOR) {
      ASS_EQ(args.size(),2);
      return replaceLits(c, lit, prox, false,
        Literal::createEquality((prox == Proxy::IFF) == positive, args[0], args[1], boolSort));
    }
  }

  return c;
}

LazyClausificationGIE::LazyClausificationGIE(SaturationAlgorithm& salg)
  : _formulaIndex(salg.getSimplifyingIndex<SkolemisingFormulaIndex>())
{}

LazyClausification::LazyClausification(SaturationAlgorithm& salg)
  : _formulaIndex(salg.getSimplifyingIndex<SkolemisingFormulaIndex>())
{}

Option<ClauseIterator> EagerClausificationISE::simplifyMany(Clause* c)
{
  auto it = produceClauses(c, false);
  if (it.hasNext()) {
    return some(it);
  }
  return none<ClauseIterator>();
}

ClauseIterator LazyClausificationGIE::generateClauses(Clause* c)
{
  return produceClauses(c, true, _formulaIndex.get());
}

ClauseIterator LazyClausification::perform(Clause* c)
{
  return produceClauses(c, false, _formulaIndex.get());
}


}
