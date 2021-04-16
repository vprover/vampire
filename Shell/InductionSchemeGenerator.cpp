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
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "InductionSchemeFilter.hpp"

using namespace Kernel;

namespace Shell {

inline bool skolem(TermList t) {
  return !t.isVar() && env.signature->getFunction(t.term()->functor())->skolem();
}

inline bool containsSkolem(TermList t)
{
  if (skolem(t)) {
    return true;
  }
  SubtermIterator stit(t.term());
  while (stit.hasNext()) {
    auto st = stit.next();
    if (env.signature->getFunction(st.term()->functor())->skolem()) {
      return true;
    }
  }
  return false;
}

inline bool canInductOn(TermList t)
{
  CALL("canInductOn");

  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();
  return skolem(t) || (complexTermsAllowed && containsSkolem(t));
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vvector<TermList> getInductionTerms(TermList t)
{
  CALL("getInductionTerms");
  // no predicates or variables here
  ASS(t.isTerm() && !t.term()->isLiteral());

  vvector<TermList> v;
  if (canInductOn(t)) {
    v.push_back(t);
  }
  unsigned f = t.term()->functor();
  auto type = env.signature->getFunction(f)->fnType();

  // If function with recursive definition,
  // recurse in its active arguments
  if (env.signature->hasInductionTemplate(f, false /*pred*/)) {
    auto& templ = env.signature->getInductionTemplate(f, false /*pred*/);
    const auto& indVars = templ._inductionPositions;

    Term::Iterator argIt(t.term());
    unsigned i = 0;
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (indVars.at(i) && type->arg(i) == type->result()) {
        auto indTerms = getInductionTerms(arg);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
      i++;
    }
  } else if (isTermAlgebraCons(t)) {
    for (unsigned i = 0; i < t.term()->arity(); i++) {
      auto st = *t.term()->nthArgument(i);
      if (type->arg(i) == type->result()) {
        auto indTerms = getInductionTerms(st);
        v.insert(v.end(), indTerms.begin(), indTerms.end());
      }
    }
  }
  return v;
}

TermList TermReplacement2::transformSubterm(TermList trm)
{
  auto rIt = _r.find(trm);
  if (rIt != _r.end()) {
    return rIt->second;
  }
  return trm;
}


TermList TermOccurrenceReplacement2::transformSubterm(TermList trm)
{
  auto rIt = _r.find(trm);
  if (rIt != _r.end()) {
    auto oIt = _o.find(make_pair(_lit,trm));
    ASS(oIt != _o.end());
    if (oIt->second.pop_last()) {
      return rIt->second;
    }
  }
  return trm;
}

TermList InductionHypothesisStrengthening::transformSubterm(TermList trm)
{
  CALL("InductionHypothesisStrengthening::transformSubterm");

  if (skolem(trm) && (!_isEq || (_lhs.containsSubterm(trm) && _rhs.containsSubterm(trm)))) {
    auto it = _r.find(trm);
    if (it == _r.end()) {
      it = _r.insert(make_pair(trm, TermList(_v++,false))).first;
    }
    return it->second;
  }
  return trm;
}

TermList TermOccurrenceReplacement::transformSubterm(TermList trm)
{
  CALL("TermOccurrenceReplacement::transformSubterm");

  auto rIt = _r.find(trm);

  // The induction generalization heuristic is stored here:
  // - if we have only one active occurrence, induct on all
  // - otherwise only induct on the active occurrences
  if (rIt != _r.end()) {
    if (!_c.find(trm)) {
      _c.insert(trm, 0);
    } else {
      _c.get(trm)++;
    }
    const auto& o = _o.get(trm);
    auto one = env.options->inductionTermOccurrenceSelectionHeuristic()
      == Options::InductionTermOccurrenceSelectionHeuristic::ONE;
    auto oc = _oc.get(trm);
    if (o->size() == 1 || (!one && oc == o->size() + 1) || o->contains(_c.get(trm))) {
      return _r.at(trm);
    }
  }
  // otherwise we may replace it with a variable
  if ((_replaceSkolem && skolem(trm)) || trm.isVar()) {
    if (!_r_g.count(trm)) {
      _r_g.insert(make_pair(trm, TermList(_v++,false)));
    }
    return _r_g.at(trm);
  }
  return trm;
}

TermList VarReplacement::transformSubterm(TermList trm)
{
  CALL("VarReplacement::transformSubterm");

  if(trm.isVar()) {
    if (!_varMap.find(trm.var())) {
      _varMap.insert(trm.var(), _v++);
    }
    return TermList(_varMap.get(trm.var()), false);
  }
  return trm;
}

TermList VarShiftReplacement::transformSubterm(TermList trm) {
  if (trm.isVar()) {
    return TermList(trm.var()+_shift, trm.isSpecialVar());
  }
  return trm;
}

bool InductionScheme::Case::contains(const InductionScheme::Case& other) const
{
  vmap<TermList, RobSubstitutionSP> substs;
  for (const auto& kv : other._step) {
    // we only check this on relations with the same
    // induction terms
    ASS (_step.count(kv.first));
    auto s2 = _step.at(kv.first);
    RobSubstitutionSP subst(new RobSubstitution);
    // try to unify the step cases
    if (!subst->unify(s2, 0, kv.second, 1)) {
      return false;
    }
    auto t1 = subst->apply(kv.second, 1);
    Renaming r1, r2;
    r1.normalizeVariables(kv.second);
    r2.normalizeVariables(s2);
    auto t2 = subst->apply(s2, 0);
    if (t1 != r1.apply(kv.second) || t2 != r2.apply(s2)) {
      return false;
    }
    substs.insert(make_pair(kv.first, subst));
  }
  // if successful, find pair for each recCall in sch1
  // don't check if recCall1 or recCall2 contain kv.first
  // as they should by definition
  for (const auto& recCall1 : other._recursiveCalls) {
    bool found = false;
    for (const auto& recCall2 : _recursiveCalls) {
      for (const auto& kv : recCall1) {
        if (!recCall1.count(kv.first) || !recCall2.count(kv.first)) {
          continue;
        }
        auto subst = substs.at(kv.first);
        const auto& r1 = subst->apply(recCall1.at(kv.first), 1);
        const auto& r2 = subst->apply(recCall2.at(kv.first), 0);
        if (r1 == r2) {
          found = true;
          break;
        }
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

bool InductionScheme::init(const vvector<TermList>& argTerms, const InductionTemplate& templ)
{
  CALL("InductionScheme::init");

  unsigned var = 0;
  const bool strengthen = env.options->inductionStrengthen();
  for (auto& b : templ._branches) {
    // for each branch, use a new substitution and variable
    // replacement as these cases should be independent
    vmap<TermList,TermList> stepSubst;
    IntList::Iterator fvIt(b._header.freeVariables());
    vset<unsigned> stepFreeVars;
    vset<unsigned> freeVars;
    while (fvIt.hasNext()) {
      stepFreeVars.insert(fvIt.next());
    }
    auto& recCalls = b._recursiveCalls;
    for (auto& r : recCalls) {
      IntList::Iterator rIt(r.freeVariables());
      while (rIt.hasNext()) {
        freeVars.insert(rIt.next());
      }
    }
    if (!includes(stepFreeVars.begin(), stepFreeVars.end(), freeVars.begin(), freeVars.end())) {
      return false;
    }
    vvector<vmap<TermList,TermList>> recCallSubstList(recCalls.size());
    vvector<bool> changed(recCalls.size(), false);
    vvector<bool> invalid(recCalls.size(), false);

    // We first map the inductive terms of t to the arguments of
    // the function header stored in the step case
    bool mismatch = false;
    RobSubstitution subst;
    for (const auto& vars : templ._order) {
      vvector<bool> changing(recCalls.size(), false);
      for (const auto& v : vars) {
        auto argTerm = argTerms.at(v);
        auto argStep = *b._header.term()->nthArgument(v);
        // This argument might have already been mapped
        if (stepSubst.count(argTerm)) {
          if (!subst.unify(stepSubst.at(argTerm), 0, argStep, 1)) {
            mismatch = true;
            break;
          }
          stepSubst.at(argTerm) = subst.apply(stepSubst.at(argTerm), 0);
        } else {
          stepSubst.insert(make_pair(argTerm, argStep));
        }
        for (unsigned i = 0; i < recCalls.size(); i++) {
          // if this recursive call is already invalid, skip it
          if (invalid[i]) {
            continue;
          }
          auto argRecCall = *recCalls[i].term()->nthArgument(v);
          if (recCallSubstList[i].count(argTerm)) {
            auto t1 = subst.apply(recCallSubstList[i].at(argTerm), 0);
            // if we would introduce here a fresh variable,
            // just save the application of unification,
            // otherwise try to unify the recursive terms
            if (!changed[i] || !strengthen) {
              auto t2 = subst.apply(argRecCall, 1);
              if (t1 != t2) {
                invalid[i] = true;
                continue;
              }
            }
            recCallSubstList[i].at(argTerm) = t1;
          } else {
            // if strengthen option is on and this
            // induction term is irrelevant for
            // the order, we add a fresh variable
            if (changed[i] && strengthen) {
              recCallSubstList[i].insert(make_pair(
                argTerm, TermList(var++, false)));
            } else {
              recCallSubstList[i].insert(make_pair(argTerm, argRecCall));
            }
          }
          // find out if this is the changing set
          if (argStep != argRecCall) {
            changing[i] = true;
          }
        }
        _inductionTerms.insert(argTerm);
      }
      if (mismatch) {
        break;
      }
      for (unsigned i = 0; i < changing.size(); i++) {
        if (changing[i]) {
          changed[i] = true;
        }
      }
    }
    if (mismatch) {
      // We cannot properly create this case because
      // there is a mismatch between the ctors for
      // a substituted term
      continue;
    }

    DHMap<unsigned, unsigned> varMap;
    VarReplacement vr(varMap, var);
    for (const auto& kv : stepSubst) {
      stepSubst.at(kv.first) = applyVarReplacement(stepSubst.at(kv.first), vr);
      for (unsigned i = 0; i < recCalls.size(); i++) {
        if (invalid[i]) {
          continue;
        }
        recCallSubstList[i].at(kv.first) = applyVarReplacement(recCallSubstList[i].at(kv.first), vr);
      }
    }

    vvector<vmap<TermList,TermList>> recCallSubstFinal;
    for (unsigned i = 0; i < recCallSubstList.size(); i++) {
      if (!invalid[i]) {
        recCallSubstFinal.push_back(recCallSubstList[i]);
      }
    }
    _cases.emplace_back(std::move(recCallSubstFinal), std::move(stepSubst));
  }
  _maxVar = var;
  // clean();
  return true;
}

void InductionScheme::init(vvector<InductionScheme::Case>&& cases)
{
  CALL("InductionScheme::init");

  _cases = cases;
  _inductionTerms.clear();
  unsigned var = 0;

  for (auto& c : _cases) {
    DHMap<unsigned, unsigned> varMap;
    VarReplacement vr(varMap, var);
    for (auto& kv : c._step) {
      kv.second = kv.second.isVar()
        ? vr.transformSubterm(kv.second)
        : TermList(vr.transform(kv.second.term()));
      _inductionTerms.insert(kv.first);
    }
    for (auto& recCall : c._recursiveCalls) {
      for (auto& kv : recCall) {
        kv.second = kv.second.isVar()
          ? vr.transformSubterm(kv.second)
          : TermList(vr.transform(kv.second.term()));
      }
    }
  }
  _maxVar = var;
  clean();
}

void InductionScheme::clean()
{
  for (unsigned i = 0; i < _cases.size(); i++) {
    for (unsigned j = i+1; j < _cases.size();) {
      if (_cases[i].contains(_cases[j])) {
        _cases[j] = _cases.back();
        _cases.pop_back();
      } else {
        j++;
      }
    }
  }
  _cases.shrink_to_fit();
}

InductionScheme InductionScheme::makeCopyWithVariablesShifted(unsigned shift) const {
  InductionScheme res;
  res._inductionTerms = _inductionTerms;
  VarShiftReplacement vsr(shift);

  for (const auto& c : _cases) {
    vvector<vmap<TermList, TermList>> resRecCalls;
    for (const auto& recCall : c._recursiveCalls) {
      vmap<TermList, TermList> resRecCall;
      for (auto kv : recCall) {
        resRecCall.insert(make_pair(kv.first,
          kv.second.isVar()
            ? vsr.transformSubterm(kv.second)
            : TermList(vsr.transform(kv.second.term()))));
      }
      resRecCalls.push_back(resRecCall);
    }
    vmap<TermList, TermList> resStep;
    for (auto kv : c._step) {
      resStep.insert(make_pair(kv.first,
        kv.second.isVar()
          ? vsr.transformSubterm(kv.second)
          : TermList(vsr.transform(kv.second.term()))));
    }
    res._cases.emplace_back(std::move(resRecCalls), std::move(resStep));
  }
  res._maxVar = _maxVar + shift;
  return res;
}

bool InductionScheme::checkWellFoundedness()
{
  vvector<pair<vmap<TermList,TermList>&,vmap<TermList,TermList>&>> relations;
  for (auto& c : _cases) {
    for (auto& recCall : c._recursiveCalls) {
      relations.push_back(
        pair<vmap<TermList,TermList>&,vmap<TermList,TermList>&>(
          recCall, c._step));
    }
  }
  return checkWellFoundedness(relations, _inductionTerms);
}

bool InductionScheme::checkWellFoundedness(
  vvector<pair<vmap<TermList,TermList>&,vmap<TermList,TermList>&>> relations,
  vset<TermList> inductionTerms)
{
  if (relations.empty()) {
    return true;
  }
  if (inductionTerms.empty()) {
    return false;
  }
  for (const auto& indTerm : inductionTerms) {
    vvector<pair<vmap<TermList,TermList>&,vmap<TermList,TermList>&>> remaining;
    bool check = true;
    for (const auto& rel : relations) {
      auto it1 = rel.first.find(indTerm);
      auto it2 = rel.second.find(indTerm);
      // if either one is missing or the step term
      // does not contain the recursive term as subterm
      if (it1 == rel.first.end() || it2 == rel.second.end()
        || !it2->second.containsSubterm(it1->second))
      {
        check = false;
        break;
      }
      if (it1->second == it2->second) {
        remaining.push_back(rel);
      }
    }
    if (check) {
      auto remIndTerms = inductionTerms;
      remIndTerms.erase(indTerm);
      if (checkWellFoundedness(remaining, std::move(remIndTerms))) {
        return true;
      }
    }
  }
  return false;
}

void InductionScheme::addBaseCases() {
  unsigned var = _maxVar;
  vvector<vmap<TermList, vvector<TermList>>> availableTermsLists(1); // contains one empty map
  for (const auto& c : _cases) {
    vvector<vmap<TermList, vvector<TermList>>> nextAvailableTermsLists;
    for (const auto& kv : c._step) {
      if (kv.second.isTerm()) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          auto pIt = availableTerms.find(kv.first);
          if (pIt == availableTerms.end()) {
            pIt = availableTerms.insert(
              make_pair(kv.first, TermAlgebra::generateAvailableTerms(kv.first.term(), var))).first;
          }
          TermAlgebra::excludeTermFromAvailables(pIt->second, kv.second, var);
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      }
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  // We have a set here so there are no duplicate cases
  vset<vmap<TermList, TermList>> steps;
  for (const auto& availableTerms : availableTermsLists) {
    vvector<vmap<TermList, TermList>> temp(1);
    auto invalid = false;
    for (const auto& kv : availableTerms) {
      if (kv.second.empty()) {
        invalid = true;
        break;
      }
      vvector<vmap<TermList, TermList>> newTemp;
      for (const auto& p : kv.second) {
        for (auto step : temp) { // intentionally copy step here
          ASS(!step.count(kv.first));
          step.insert(make_pair(kv.first, p));
          newTemp.push_back(step);
        }
      }
      temp = newTemp;
    }
    if (!invalid) {
      steps.insert(temp.begin(), temp.end());
    }
  }

  // each step gets an empty recursive call and condition set
  var = _maxVar;
  for (auto step : steps) {
    vvector<vmap<TermList,TermList>> emptyRecCalls;
    DHMap<unsigned, unsigned> varMap;
    VarReplacement vr(varMap, var);
    for (auto& kv : step) {
      kv.second = applyVarReplacement(kv.second, vr);
    }
    _cases.emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  _maxVar = var;
}

ostream& operator<<(ostream& out, const InductionScheme& scheme)
{
  unsigned k = 0;
  unsigned l = scheme._inductionTerms.size();
  for (const auto& indTerm : scheme._inductionTerms) {
    out << indTerm;
    if (++k < l) {
      out << ',';
    }
  }
  out << ':';
  unsigned j = 0;
  for (const auto& c : scheme._cases) {
    unsigned i = 0;
    for (const auto& recCall : c._recursiveCalls) {
      out << '[';
      k = 0;
      for (const auto& indTerm : scheme._inductionTerms) {
        auto it = recCall.find(indTerm);
        out << ((it != recCall.end()) ? it->second.toString() : "_");
        if (++k < l) {
          out << ',';
        }
      }
      out << ']';
      if (++i < c._recursiveCalls.size()) {
        out << ',';
      }
    }
    if (!c._recursiveCalls.empty()) {
      out << "=>";
    }
    k = 0;
    out << '[';
    for (const auto& indTerm : scheme._inductionTerms) {
      auto it = c._step.find(indTerm);
      out << ((it != c._step.end()) ? it->second.toString() : "_");
      if (++k < l) {
        out << ',';
      }
      k++;
    }
    out << ']';
    if (++j < scheme._cases.size()) {
      out << ';';
    }
  }

  return out;
}

void RecursionInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vvector<SLQueryResult>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("RecursionInductionSchemeGenerator()");

  vvector<InductionScheme> primarySchemes;
  vvector<InductionScheme> secondarySchemes;
  _actOccMaps.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  static bool simplify = env.options->simplifyBeforeInduction();
  if (!generate(main.clause, main.literal, primarySchemes, simplify)) {
    return;
  }
  for (const auto& s : side) {
    if (litsProcessed.insert(s.literal).second) {
      generate(s.clause, s.literal, secondarySchemes, false);
    }
  }
  for (auto& o : _actOccMaps) {
    o.second.finalize();
  }
  InductionSchemeFilter f;
  f.filter(primarySchemes, secondarySchemes);
  f.filterComplex(primarySchemes, _actOccMaps);

  for (const auto& sch : primarySchemes) {
    OccurrenceMap necessary;
    for (const auto& kv : _actOccMaps) {
      if (sch._inductionTerms.count(kv.first.second)) {
        necessary.insert(kv);
      }
    }
    res.push_back(make_pair(sch, necessary));
  }
}

bool RecursionInductionSchemeGenerator::generate(Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes, bool returnOnMatch)
{
  CALL("InductionSchemeGenerator::generate");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  Stack<bool> actStack;
  if (lit->isEquality()) {
    actStack.push(true);
    actStack.push(true);
  } else {
    if (!process(TermList(lit), true, actStack, premise, lit, schemes, returnOnMatch)
        /* short circuit */ && returnOnMatch) {
      return false;
    }
  }
  SubtermIterator it(lit);
  while(it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    if (!process(curr, active, actStack, premise, lit, schemes, returnOnMatch)
        /* short circuit */ && returnOnMatch) {
      return false;
    }
  }
  ASS(actStack.isEmpty());
  return true;
}

bool RecursionInductionSchemeGenerator::process(TermList curr, bool active,
  Stack<bool>& actStack, Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes,
  bool returnOnMatch)
{
  CALL("InductionSchemeGenerator::process");

  if (!curr.isTerm()) {
    return true;
  }
  auto t = curr.term();

  // If induction term, store the occurrence
  if (canInductOn(curr)) {
    auto p = make_pair(lit,curr);
    auto aIt = _actOccMaps.find(p);
    if (aIt == _actOccMaps.end()) {
      _actOccMaps.insert(make_pair(p, Occurrences(active)));
    } else {
      aIt->second.add(active);
    }
  }

  unsigned f = t->functor();
  bool isPred = t->isLiteral();

  // If function with recursive definition, create a scheme
  if (env.signature->hasInductionTemplate(f, isPred)) {
    auto& templ = env.signature->getInductionTemplate(f, isPred);
    const auto& indVars = templ._inductionPositions;

    for (auto it = indVars.rbegin(); it != indVars.rend(); it++) {
      actStack.push(*it && active);
    }

    if (returnOnMatch) {
      for (const auto& b : templ._branches) {
        if (MatchingUtils::matchTerms(b._header, curr)) {
          return false;
        }
      }
    }

    if (!active) {
      return true;
    }

    Term::Iterator argIt(t);
    unsigned i = 0;
    vvector<vvector<TermList>> argTermsList(1); // initially 1 empty vector
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (!indVars[i]) {
        for (auto& argTerms : argTermsList) {
          argTerms.push_back(arg);
        }
      } else {
        auto its = getInductionTerms(arg);
        vvector<vvector<TermList>> newArgTermsList;
        for (const auto& indTerm : its) {
          for (auto argTerms : argTermsList) {
            argTerms.push_back(indTerm);
            newArgTermsList.push_back(std::move(argTerms));
          }
        }
        argTermsList = newArgTermsList;
      }
      i++;
    }

    for (const auto& argTerms : argTermsList) {
      InductionScheme scheme;
      if (!scheme.init(argTerms, templ)) {
        continue;
      }
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] induction scheme " << scheme
                  << " was suggested by term " << *t << " in " << *lit << endl;
        env.endOutput();
      }
      schemes.push_back(std::move(scheme));
    }
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
    }
  }
  return true;
}

void RecursionInductionSchemeGenerator2::generate(
  const SLQueryResult& main,
  const vvector<SLQueryResult>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("RecursionInductionSchemeGenerator2::generate()");

  vvector<InductionScheme> primarySchemes;
  vvector<InductionScheme> secondarySchemes;
  _actOccMaps.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal, primarySchemes);
  for (const auto& s : side) {
    if (litsProcessed.insert(s.literal).second) {
      generate(s.clause, s.literal, secondarySchemes);
    }
  }
  for (auto& o : _actOccMaps) {
    o.second.finalize();
  }
  InductionSchemeFilter f;
  f.filter(primarySchemes, secondarySchemes);
  f.filterComplex(primarySchemes, _actOccMaps);

  for (const auto& sch : primarySchemes) {
    OccurrenceMap necessary;
    for (const auto& kv : _actOccMaps) {
      if (sch._inductionTerms.count(kv.first.second)) {
        necessary.insert(kv);
      }
    }
    res.push_back(make_pair(sch, necessary));
  }
}

void RecursionInductionSchemeGenerator2::generate(Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes)
{
  CALL("RecursionInductionSchemeGenerator2::generate");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  Stack<bool> actStack;
  if (lit->isEquality()) {
    actStack.push(true);
    actStack.push(true);
  } else {
    process(TermList(lit), true, actStack, premise, lit, schemes);
  }
  SubtermIterator it(lit);
  while(it.hasNext()){
    TermList curr = it.next();
    bool active = actStack.pop();
    process(curr, active, actStack, premise, lit, schemes);
  }
  ASS(actStack.isEmpty());
}

void RecursionInductionSchemeGenerator2::process(TermList curr, bool active,
  Stack<bool>& actStack, Clause* premise, Literal* lit,
  vvector<InductionScheme>& schemes)
{
  CALL("RecursionInductionSchemeGenerator2::process");

  if (!curr.isTerm()) {
    return;
  }
  auto t = curr.term();

  // If induction term, store the occurrence
  if (canInductOn(curr)) {
    auto p = make_pair(lit,curr);
    auto aIt = _actOccMaps.find(p);
    if (aIt == _actOccMaps.end()) {
      _actOccMaps.insert(make_pair(p, Occurrences(active)));
    } else {
      aIt->second.add(active);
    }
  }

  unsigned f = t->functor();
  bool isPred = t->isLiteral();

  // If function with recursive definition, create a scheme
  if (env.signature->hasInductionTemplate(f, isPred)) {
    auto& templ = env.signature->getInductionTemplate(f, isPred);
    const auto& indPos = templ._inductionPositions;

    for (int i = t->arity()-1; i >= 0; i--) {
      actStack.push(indPos[i] && active);
    }

    if (!active) {
      return;
    }

    TermStack args;
    unsigned var = 0;
    vmap<TermList, unsigned> varMap;
    for (unsigned i = 0; i < t->arity(); i++) {
      auto arg = *t->nthArgument(i);
      if (indPos[i]) {
        if (!containsSkolem(arg)) {
          return;
        }
        auto it = varMap.find(arg);
        if (it == varMap.end()) {
          it = varMap.insert(make_pair(arg, var++)).first;
        }
        args.push(TermList(it->second, false));
      } else {
        args.push(arg);
      }
    }
    InductionScheme scheme;
    TermList genTerm(Term::create(t, args.begin()));
    for (const auto& b : templ._branches) {
      RobSubstitutionSP subst(new RobSubstitution);
      if (subst->unify(b._header, 0, genTerm, 1)) {
        auto headerS = subst->apply(b._header, 0);
        auto headerST = headerS.term();
        vmap<TermList, TermList> mainSubst;
        for (unsigned i = 0; i < t->arity(); i++) {
          if (indPos[i]) {
            mainSubst.insert(make_pair(*t->nthArgument(i), *headerST->nthArgument(i)));
            scheme._inductionTerms.insert(*t->nthArgument(i));
          }
        }
        vvector<vmap<TermList, TermList>> hypSubsts;
        for (const auto& recCall : b._recursiveCalls) {
          auto recCallS = subst->apply(recCall, 0);
          auto recCallST = recCallS.term();
          hypSubsts.emplace_back();
          for (unsigned i = 0; i < t->arity(); i++) {
            auto rarg = *recCallST->nthArgument(i);
            auto arg = *t->nthArgument(i);
            if (indPos[i]) {
              hypSubsts.back().insert(make_pair(arg, rarg));
            } else if (rarg != *headerST->nthArgument(i) && containsSkolem(arg)) {
              // mainSubst.insert(make_pair(arg, *headerST->nthArgument(i)));
              hypSubsts.back().insert(make_pair(arg, rarg));
              scheme._inductionTerms.insert(arg);
            }
          }
        }
        scheme._cases.emplace_back(std::move(hypSubsts), std::move(mainSubst));
      }
    }
    scheme.addBaseCases();
    if (!scheme.checkWellFoundedness()) {
      return;
    }

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] induction scheme " << scheme
                << " was suggested by term " << *t << " in " << *lit << endl;
      env.endOutput();
    }
    schemes.push_back(std::move(scheme));
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      actStack.push(active);
    }
  }
}

void StructuralInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vvector<SLQueryResult>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("StructuralInductionSchemeGenerator()");

  vvector<InductionScheme> schemes;
  OccurrenceMap occMap;

  static Options::InductionChoice kind = env.options->inductionChoice();
  static bool all = (kind == Options::InductionChoice::ALL);
  static bool goal_plus = (kind == Options::InductionChoice::GOAL_PLUS);
  static bool structInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::STRUCTURAL;
  static bool mathInd = env.options->induction() == Options::Induction::BOTH ||
                         env.options->induction() == Options::Induction::MATHEMATICAL;
  static bool complexTermsAllowed = env.options->inductionOnComplexTerms();

  Set<Term*> ta_terms;
  Set<Term*> int_terms;
  SubtermIterator it(main.literal);
  while(it.hasNext()){
    TermList ts = it.next();
    ASS(ts.isTerm());
    unsigned f = ts.term()->functor();
    if((complexTermsAllowed || env.signature->functionArity(f)==0) &&
        (
            all
        || env.signature->getFunction(f)->inGoal()
        || (goal_plus && env.signature->getFunction(f)->inductionSkolem()) // set in NewCNF
        )
    ){
      if(structInd &&
        env.signature->isTermAlgebraSort(env.signature->getFunction(f)->fnType()->result()) &&
        ((complexTermsAllowed && env.signature->functionArity(f) != 0) || !env.signature->getFunction(f)->termAlgebraCons()) // skip base constructors
        ){
        ta_terms.insert(ts.term());
      }
      if(mathInd &&
          env.signature->getFunction(f)->fnType()->result()==Sorts::SRT_INTEGER &&
          !theory->isInterpretedConstant(f)
        ){
        int_terms.insert(ts.term());
      }
    }
    auto p = make_pair(main.literal, ts);
    auto oIt = occMap.find(p);
    if (oIt == occMap.end()) {
      occMap.insert(make_pair(p, Occurrences(false)));
    } else {
      oIt->second.add(false);
    }
  }

  Set<Term*>::Iterator taIt(ta_terms);
  while (taIt.hasNext()) {
    schemes.push_back(generateStructural(taIt.next()));
  }

  for (const auto& qr : side) {
    SubtermIterator it(qr.literal);
    while(it.hasNext()){
      TermList ts = it.next();
      auto p = make_pair(qr.literal, ts);
      auto oIt = occMap.find(p);
      if (oIt == occMap.end()) {
        occMap.insert(make_pair(p, Occurrences(false)));
      } else {
        oIt->second.add(false);
      }
    }
  }

  for (auto& o : occMap) {
    o.second.finalize();
  }

  for (const auto& sch : schemes) {
    OccurrenceMap necessary;
    for (const auto& kv : occMap) {
      if (sch._inductionTerms.count(kv.first.second)) {
        necessary.insert(kv);
      }
    }
    res.push_back(make_pair(sch, necessary));
  }
}

InductionScheme StructuralInductionSchemeGenerator::generateStructural(Term* term)
{
  CALL("StructuralInductionSchemeGenerator::generateStructural");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  unsigned ta_sort = ta->sort();
  unsigned var = 0;
  InductionScheme scheme;

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* con = ta->constructor(i);
    vvector<vmap<TermList,TermList>> recursiveCalls;
    vmap<TermList,TermList> step;

    unsigned arity = con->arity();
    Stack<TermList> ta_vars;
    Stack<TermList> argTerms;
    for (unsigned i = 0; i < arity; i++) {
      TermList x(var++,false);
      argTerms.push(x);
      if(con->argSort(i) == ta_sort){
        ta_vars.push(x);
      }
    }
    Stack<TermList>::Iterator tvit(ta_vars);
    while (tvit.hasNext()) {
      vmap<TermList, TermList> recCall;
      recCall.insert(make_pair(term,tvit.next()));
      recursiveCalls.push_back(recCall);
    }
    step.insert(make_pair(term,
      TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()))));
    scheme._cases.emplace_back(std::move(recursiveCalls), std::move(step));
  }
  scheme._inductionTerms.insert(TermList(term));
  scheme._maxVar = var;
  return scheme;
}

} // Shell
