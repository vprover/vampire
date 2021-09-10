/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionSchemeGenerator.hpp"

#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Inferences/InductionHelper.hpp"

using namespace Kernel;

namespace Shell {

inline bool isTermAlgebraCons(Term* t)
{
  ASS(!t->isLiteral());
  return env.signature->getFunction(t->functor())->termAlgebraCons();
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vset<Term*> getInductionTerms(Term* t)
{
  CALL("getInductionTerms");
  // no predicates here
  ASS(!t->isLiteral());

  vset<Term*> res;
  Stack<Term*> todo;
  todo.push(t);

  while (todo.isNonEmpty()) {
    auto curr = todo.pop();

    if (res.count(curr)) {
      continue;
    }

    if (canInductOn(curr)) {
      res.insert(curr);
    }
    unsigned f = curr->functor();
    auto type = env.signature->getFunction(f)->fnType();

    // If function with recursive definition,
    // recurse in its active arguments
    if (env.signature->getFnDefHandler()->hasInductionTemplate(f, true /*trueFun*/)) {
      auto& templ = env.signature->getFnDefHandler()->getInductionTemplate(f, true /*trueFun*/);
      const auto& indVars = templ.inductionPositions();

      Term::Iterator argIt(curr);
      unsigned i = 0;
      while (argIt.hasNext()) {
        auto arg = argIt.next();
        if (indVars.at(i) && type->arg(i) == type->result() && arg.isTerm()) {
          todo.push(arg.term());
        }
        i++;
      }
    } else if (isTermAlgebraCons(curr)) {
      for (unsigned i = 0; i < curr->arity(); i++) {
        if (type->arg(i) == type->result()) {
          auto st = *curr->nthArgument(i);
          if (st.isTerm()) {
            todo.push(st.term());
          }
        }
      }
    } else {
      for (unsigned i = 0; i < curr->arity(); i++) {
        auto st = *curr->nthArgument(i);
        if (st.isTerm()) {
          todo.push(st.term());
        }
      }
    }
  }
  return res;
}

void RecursionInductionSchemeGenerator::generate(
  const InductionPremises& premises,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("RecursionInductionSchemeGenerator::generate/1");

  _schemes.clear();
  _actOccMaps._m.clear();

  const InductionPremise& main = premises.main();
  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal);
  for (const InductionPremise& s : premises.sides()) {
    if (litsProcessed.insert(s.literal).second) {
      generate(s.clause, s.literal);
    }
  }
  _actOccMaps.finalize();
  // filter out schemes that only contain induction
  // terms not present in the main literal
  for (auto it = _schemes.begin(); it != _schemes.end();) {
    static const bool filterC = env.options->inductionOnComplexTermsHeuristic();
    bool filter = true;
    for (const auto& kv : it->inductionTerms()) {
      auto c = !skolem(kv.first);
      unsigned occ = 0;
      for (const auto& kv2 : _actOccMaps._m) {
        if (kv.first == kv2.first.second) {
          if (c) {
            occ += kv2.second.num_bits();
          }
          if (kv2.first.first == main.literal && kv2.second.num_set_bits()) {
            filter = false;
          }
        }
      }
      if (filterC && occ == 1) {
        filter = true;
        break;
      }
    }
    if (filter) {
      it = _schemes.erase(it);
    } else {
      it++;
    }
  }

  for (const auto& sch : _schemes) {
    res.push_back(make_pair(sch, _actOccMaps.create_necessary(sch)));
  }
}

void RecursionInductionSchemeGenerator::generate(Clause* premise, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::generate/2");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] processing literal " << *lit << endl;
    env.endOutput();
  }

  Stack<bool> actStack;
  process(lit, actStack);
  SubtermIterator it(lit);
  while (it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    if (curr.isTerm()) {
      process(curr.term(), active, actStack, lit);
    }
  }
  ASS(actStack.isEmpty());
}

void RecursionInductionSchemeGenerator::handleActiveTerm(Term* t, InductionTemplate& templ, Stack<bool>& actStack)
{
  CALL("RecursionInductionSchemeGenerator::handleActiveTerm");

  const auto& indPos = templ.inductionPositions();

  for (int i = t->arity()-1; i >= 0; i--) {
    actStack.push(indPos[i]);
  }

  static bool exhaustive = env.options->inductionExhaustiveGeneration();
  if (exhaustive) {
    Term::Iterator argIt(t);
    unsigned i = 0;
    vvector<TermStack> argTermsList(1); // initially 1 empty vector
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (!indPos[i] || arg.isVar()) {
        for (auto& argTerms : argTermsList) {
          argTerms.push(arg);
        }
      } else {
        auto its = getInductionTerms(arg.term());
        vvector<TermStack> newArgTermsList;
        for (const auto& indTerm : its) {
          for (auto argTerms : argTermsList) {
            argTerms.push(TermList(indTerm));
            newArgTermsList.push_back(std::move(argTerms));
          }
        }
        argTermsList = newArgTermsList;
      }
      i++;
    }

    auto isLit = t->isLiteral();
    for (const auto& argTerms : argTermsList) {
      Term* nt;
      if (isLit) {
        nt = Literal::create(static_cast<Literal*>(t), argTerms.begin());
      } else {
        nt = Term::create(t, argTerms.begin());
      }
      templ.requestInductionScheme(nt, _schemes);
    }
  } else {
    templ.requestInductionScheme(t, _schemes);
  }
}

void RecursionInductionSchemeGenerator::process(Term* t, bool active,
  Stack<bool>& actStack, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::process");

  // If induction term, store the occurrence
  if (canInductOn(t)) {
    _actOccMaps.add(lit, t, active);
  }

  unsigned f = t->functor();

  // If function with recursive definition, create a scheme
  if (active && env.signature->getFnDefHandler()->hasInductionTemplate(f, true)) {
    handleActiveTerm(t, env.signature->getFnDefHandler()->getInductionTemplate(f, true), actStack);
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
    }
  }
}

void RecursionInductionSchemeGenerator::process(Literal* lit, Stack<bool>& actStack)
{
  CALL("RecursionInductionSchemeGenerator::process");

  unsigned f = lit->functor();

  // If function with recursive definition, create a scheme
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, false)) {
    handleActiveTerm(lit, env.signature->getFnDefHandler()->getInductionTemplate(f, false), actStack);
  } else {
    for (unsigned i = 0; i < lit->arity(); i++) {
      actStack.push(true);
    }
  }
}

void StructuralInductionSchemeGenerator::generate(
  const InductionPremises& premises,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("StructuralInductionSchemeGenerator::generate");

  vvector<InductionScheme> schemes;
  OccurrenceMap occMap;

  const InductionPremise& main = premises.main();
  Set<Term*> ta_terms;
  SubtermIterator it(main.literal);
  while (it.hasNext()) {
    TermList ts = it.next();
    ASS(ts.isTerm());
    Term* t = ts.term();
    unsigned f = t->functor();
    if (Inferences::InductionHelper::isInductionTerm(t) &&
        Inferences::InductionHelper::isStructInductionFunctor(f)) {
      ta_terms.insert(t);
    }
    occMap.add(main.literal, t, false);
  }

  Set<Term*>::Iterator taIt(ta_terms);
  while (taIt.hasNext()) {
    env.signature->getFnDefHandler()->requestStructuralInductionScheme(taIt.next(), schemes);
  }

  for (const InductionPremise& s : premises.sides()) {
    SubtermIterator it(s.literal);
    while (it.hasNext()) {
      Term* t = it.next().term();
      occMap.add(s.literal, t, false);
    }
  }

  occMap.finalize();
  for (const auto& sch : schemes) {
    res.push_back(make_pair(sch, occMap.create_necessary(sch)));
  }
}

void addBoundOccurrenceIfEligible(const Set<Term*>& int_terms, vmap<Term*, vset<const InductionPremise*>>& bounds, OccurrenceMap& occMap, const InductionPremise& ip) {
  ASS(Inferences::InductionHelper::isIntegerComparison(ip.clause));
  if (ip.literal->ground()) {
    for (int i = 0; i < 2; ++i) {
      Term* t = ip.literal->nthArgument(i)->term();
      if (int_terms.contains(t) && !ip.literal->nthArgument(1^i)->term()->containsSubterm(TermList(t))) {
        occMap.add(ip.literal, t, /*active=*/true);
        ASS(bounds.count(t) != 0);
        bounds[t].insert(&ip);
      }
    }
  }
}

void IntegerInductionSchemeGenerator::generate(
  const InductionPremises& premises,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("IntegerInductionSchemeGenerator::generate");

  vvector<InductionScheme> schemes;
  OccurrenceMap occMap;
  const InductionPremise& main = premises.main();

  // Extract suitable terms from main, add them to occMap, and for each induction term
  // initialize an empty sets of bounds.
  Set<Term*> int_terms;
  vmap<Term*, vset<const InductionPremise*>> bounds;
  SubtermIterator it(main.literal);
  while (it.hasNext()) {
    TermList ts = it.next();
    ASS(ts.isTerm());
    Term* t = ts.term();
    unsigned f = t->functor();
    if (Inferences::InductionHelper::isInductionTermFunctor(f) &&
        Inferences::InductionHelper::isIntInductionTermListInLiteral(ts, main.literal)) {
      int_terms.insert(t);
      occMap.add(main.literal, t, false);
      if (bounds.count(t) == 0) bounds[t] = vset<const InductionPremise*>();
    }
  }
  // Add term occurrences from bounds and sides to occMap, and add pointers
  // to relevant bounds to 'bounds' (indexed by the induction term)
  for (const InductionPremise& ip : premises.bounds()) {
    addBoundOccurrenceIfEligible(int_terms, bounds, occMap, ip);
  }
  for (const InductionPremise& ip : premises.sides()) {
    // premises.sides might contain literals usable as bounds
    if (Inferences::InductionHelper::isIntegerComparison(ip.clause)) {
      addBoundOccurrenceIfEligible(int_terms, bounds, occMap, ip);
    }
    SubtermIterator it(ip.literal);
    while (it.hasNext()) {
      TermList tl = it.next();
      Term* t = tl.term();
      if (int_terms.contains(t) && Inferences::InductionHelper::isIntInductionTermListInLiteral(tl, ip.literal)) {
        bool isBound = false;
        for (const InductionPremise* bound : bounds[t]) {
          if (bound->literal == ip.literal) {
            isBound = true;
            break;
          }
        }
        // if ip cannot be used as a bound for t, it can be used as a side
        if (!isBound) {
          occMap.add(ip.literal, t, false);
        }
      }
    } 
  }
  // For each induction term, extract suitable upper/lower bounds,
  // and generate upwards/downwards induction schemes.
  Set<Term*>::Iterator intIt(int_terms);
  while (intIt.hasNext()) {
    Term* t = intIt.next();
    TermList tl(t);
    vvector<pair<TermList*, const InductionPremise*>> lowerBounds;
    vvector<pair<TermList*, const InductionPremise*>> upperBounds;
    for (const InductionPremise* ip : bounds[t]) {
      TermList* b;
      if ((b = Inferences::InductionHelper::getLowerBoundForTermListFromLiteral(tl, ip->literal))) {
        lowerBounds.emplace_back(b, ip);
      } else if ((b = Inferences::InductionHelper::getUpperBoundForTermListFromLiteral(tl, ip->literal))) {
        upperBounds.emplace_back(b, ip);
      }
    }
    getIntegerInductionSchemes(t, lowerBounds, upperBounds, /*upward=*/ true, main.originalPremise, schemes);
    getIntegerInductionSchemes(t, upperBounds, lowerBounds, /*upward=*/ false, main.originalPremise, schemes);
  }

  occMap.finalize();
  for (const auto& sch : schemes) {
    res.push_back(make_pair(sch, occMap.create_necessary(sch)));
  }
}

void IntegerInductionSchemeGenerator::getIntegerInductionSchemes(Term* t,
    const vvector<pair<TermList*, const InductionPremise*>>& bounds1,
    const vvector<pair<TermList*, const InductionPremise*>>& bounds2,
    bool upward,
    bool mainIsOriginalPremise,
    vvector<InductionScheme>& schemes) {
  static const bool infInterval = Inferences::InductionHelper::isInductionForInfiniteIntervalsOn();
  static const bool finInterval = Inferences::InductionHelper::isInductionForFiniteIntervalsOn();
  static const bool defaultBound = env.options->integerInductionDefaultBound();
  static const bool defaultBound2 = env.options->integerInductionSecondDefaultBound();
  static const TermList zero(theory->representConstant(IntegerConstantType(0)));
  vmap<Term*, unsigned> inductionTerms;
  bool doneZero = false;
  Literal* zeroLit = nullptr;
  inductionTerms.insert(make_pair(t, 0));
  for (const pair<TermList*, const InductionPremise*>& b1 : bounds1) {
    ASS(b1.first != nullptr);
    ASS(b1.second != nullptr);
    vvector<InductionScheme::Case>* cases = getCasesForBoundAndDirection(*b1.first, upward);
    // Induction scheme with only 1 bound
    if (infInterval && (mainIsOriginalPremise || b1.second->originalPremise)) {
      makeAndPushScheme(inductionTerms, cases, b1.second->literal, /*optionalBound2=*/nullptr,
          schemes, upward);
      if (defaultBound && (*b1.first == zero)) {
        doneZero = true;
        zeroLit = b1.second->literal;
      }
    }
    // Induction schemes with 2 bounds
    if (finInterval) {
      for (const pair<TermList*, const InductionPremise*>& b2 : bounds2) {
        ASS(b2.first != nullptr);
        ASS(b2.second != nullptr);
        if ((mainIsOriginalPremise || b1.second->originalPremise || b2.second->originalPremise) &&
            (*b1.first != *b2.first)) {
          makeAndPushScheme(inductionTerms, cases, b1.second->literal, b2.second->literal,
              schemes, upward);
        }
      }
    }
  }
  // Induction scheme with the default bound
  if (defaultBound && mainIsOriginalPremise) {
    TermList tt(t);
    static const unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
    vvector<InductionScheme::Case>* cases = getCasesForBoundAndDirection(zero, upward);
    if (infInterval && !doneZero) {
      makeAndPushScheme(inductionTerms, cases,
          Literal::create2(less, /*polarity=*/false, upward ? tt : zero, upward ? zero : tt), /*optionalBound2=*/nullptr,
          schemes, upward, /*defaultBound=*/true);
    }
    if (finInterval && defaultBound2 && (tt != zero)) {
      makeAndPushScheme(inductionTerms, cases,
          doneZero ? zeroLit :
              Literal::create2(less, /*polarity=*/false, upward ? tt : zero, upward ? zero : tt),
          Literal::create2(less, /*polarity=*/false, tt, tt),
          schemes, upward, /*defaultBound=*/!doneZero, /*secondDefaultBound=*/true);
    }
  }
}

vvector<InductionScheme::Case>* IntegerInductionSchemeGenerator::getCasesForBoundAndDirection(
    const TermList& bound, bool upward) {
  ASS(bound.isTerm());
  auto it = _baseCaseMap.find(make_pair(bound.term(), upward));
  if (it != _baseCaseMap.end()) return &it->second;
  static TermList v1(1, false);
  vvector<InductionScheme::Case> cases;
  // base case substitution: x -> bound
  cases.emplace_back();
  cases.back()._step.bind(0, bound);
  // recursive calls: {x -> x}
  vvector<Substitution> recCalls;
  recCalls.emplace_back();
  recCalls.back().bind(0, v1);
  // step substitution: x -> x+1
  TermList one(theory->representConstant(IntegerConstantType(upward ? 1 : -1)));
  Substitution step;
  step.bind(0, TermList((Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS), v1, one))));
  cases.emplace_back(std::move(recCalls), std::move(step));
  return &_baseCaseMap.insert(make_pair(make_pair(bound.term(), upward), std::move(cases))).first->second;
}

void IntegerInductionSchemeGenerator::makeAndPushScheme(vmap<Term*, unsigned>& inductionTerms,
    vvector<InductionScheme::Case>* cases,
    Literal* bound1, Literal* optionalBound2,
    vvector<InductionScheme>& schemes,
    bool upward, bool defaultBound, bool secondDefaultBound) {
  InferenceRule rule =
      (defaultBound || secondDefaultBound) ? (upward ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM
                                                     : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
                                           : (optionalBound2 ? (upward ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM
                                                                       : InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM)
                                                             : (upward ? InferenceRule::INT_INF_UP_INDUCTION_AXIOM
                                                                       : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));
  InductionScheme scheme(inductionTerms, true, rule);
  scheme._cases = cases;
  scheme._bound1 = bound1;
  scheme._optionalBound2 = optionalBound2;
  scheme._integer = true;
  scheme._upward = upward;
  scheme._defaultBound = defaultBound;
  scheme._secondDefaultBound = secondDefaultBound;
  scheme.finalize();
  schemes.push_back(std::move(scheme));
}

} // Shell
