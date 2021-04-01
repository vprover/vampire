/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionSchemeFilter.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

inline TermList applySubstAndVarReplacement(TermList t, const RobSubstitution& subst, unsigned bank, VarReplacement& vr) {
  return applyVarReplacement(subst.apply(t, bank), vr);
}

bool checkContainsRecCall(const vmap<TermList, TermList>& recCall1, const vmap<TermList, TermList>& recCall2, const vmap<TermList, TermList>& step)
{
  static bool strengthen = env.options->inductionStrengthen();
  for (auto kv : step) {
    auto it1 = recCall1.find(kv.first);
    auto it2 = recCall2.find(kv.first);
    if (it1 != recCall1.end() && it2 != recCall2.end()) {
      // the second is strengthened or the first is not strengthened and they are not the same
      if (it1->second != it2->second && (!kv.second.containsSubterm(it2->second) || kv.second.containsSubterm(it1->second))) {
        return false;
      }
    } else if (it2 != recCall2.end()) {
      // the first cannot be strengthened or the second is strengthened
      if (!strengthen || !kv.second.containsSubterm(it2->second)) {
        return false;
      }
    } else if (it1 != recCall1.end()) {
      // the second cannot be strengthened
      if (!strengthen) {
        return false;
      }
    }
  }
  return true;
}

bool beforeMergeCheck(const InductionScheme& sch1, const InductionScheme& sch2) {
  // If one of the induction terms from sch2 contains
  // one from sch1, it means that those subterms are also
  // in active positions and we lose some structure
  // of sch1 if we discard it because of subsumption
  for (auto t1 : sch1._inductionTerms) { // copy here because of const
    for (auto t2 : sch2._inductionTerms) {
      if (t1 != t2 && (t2.containsSubterm(t1) || t1.containsSubterm(t2))) {
        return false;
      }
    }
  }
  return true;
}

bool createMergedCase(const InductionScheme::Case& case1, const InductionScheme::Case& case2,
  const vset<TermList>& combinedInductionTerms, InductionScheme::Case& res, unsigned& var)
{
  vmap<TermList, TermList> step;
  vmap<TermList, RobSubstitutionSP> substs;
  vmap<TermList, DHMap<unsigned, unsigned>> varMaps;
  vmap<TermList, VarReplacement> varReplacements;
  for (const auto& indTerm : combinedInductionTerms) {
    auto it1 = case1._step.find(indTerm);
    auto it2 = case2._step.find(indTerm);
    ASS(it1 != case1._step.end() || it2 != case2._step.end());
    varMaps.insert(make_pair(indTerm, DHMap<unsigned, unsigned>()));
    VarReplacement vr(varMaps.at(indTerm), var);
    if (it1 != case1._step.end() && it2 != case2._step.end()) {
      auto t1 = it1->second;
      auto t2 = it2->second;
      RobSubstitutionSP subst(new RobSubstitution);
      if (!subst->unify(t1, 0, t2, 1)) {
        return false;
      }
      step.insert(make_pair(indTerm, applySubstAndVarReplacement(t1, *subst, 0, vr)));
      substs.insert(make_pair(indTerm, subst));
    } else if (it1 != case1._step.end()) {
      step.insert(make_pair(indTerm, applyVarReplacement(it1->second, vr)));
    } else if (it2 != case2._step.end()) {
      step.insert(make_pair(indTerm, applyVarReplacement(it2->second, vr)));
    }
    varReplacements.insert(make_pair(indTerm, vr));
  }
  vvector<vmap<TermList, TermList>> recCalls;
  auto recCallFn = [&substs, &varReplacements, &recCalls](const InductionScheme::Case& c, unsigned bank) {
    for (const auto& recCall : c._recursiveCalls) {
      vmap<TermList, TermList> resRecCall;
      for (const auto& kv : recCall) {
        resRecCall.insert(make_pair(kv.first,
          (substs.count(kv.first)) ?
            applySubstAndVarReplacement(kv.second, *substs.at(kv.first), bank, varReplacements.at(kv.first)) :
            applyVarReplacement(kv.second, varReplacements.at(kv.first))));
      }
      recCalls.push_back(resRecCall);
    }
  };
  recCallFn(case1, 0);
  recCallFn(case2, 1);
  for (unsigned i = 0; i < recCalls.size(); i++) {
    for (unsigned j = i+1; j < recCalls.size();) {
      if (checkContainsRecCall(recCalls[j], recCalls[i], step)) {
        recCalls[j] = recCalls.back();
        recCalls.pop_back();
      } else {
        j++;
      }
    }
  }

  res = InductionScheme::Case(std::move(recCalls), std::move(step));
  return true;
}

void addBaseCases(InductionScheme& sch) {
  unsigned var = sch._maxVar;
  vvector<vmap<TermList, vvector<TermList>>> availableTermsLists(1); // contains one empty map
  for (const auto& c : sch._cases) {
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
  var = sch._maxVar;
  for (auto step : steps) {
    vvector<vmap<TermList,TermList>> emptyRecCalls;
    DHMap<unsigned, unsigned> varMap;
    VarReplacement vr(varMap, var);
    for (auto& kv : step) {
      kv.second = applyVarReplacement(kv.second, vr);
    }
    sch._cases.emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  sch._maxVar = var;
}

bool InductionSchemeFilter::mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res) {
  // copy original schemes in case we fail and we modified them
  InductionScheme sch1copy = sch1;
  InductionScheme sch2copy = sch2.makeCopyWithVariablesShifted(sch1copy._maxVar+1);
  if (!sch1copy.checkWellFoundedness() || !sch2copy.checkWellFoundedness()) {
    return false;
  }

  if (!includes(sch1._inductionTerms.begin(), sch1._inductionTerms.end(),
      sch2._inductionTerms.begin(), sch2._inductionTerms.end()) &&
      !includes(sch2._inductionTerms.begin(), sch2._inductionTerms.end(),
      sch1._inductionTerms.begin(), sch1._inductionTerms.end())) {
    return false;
  }
  vset<TermList> combinedInductionTerms = sch1._inductionTerms;
  combinedInductionTerms.insert(sch2._inductionTerms.begin(), sch2._inductionTerms.end());

  vvector<InductionScheme::Case> resCases;
  unsigned var = 0;
  for (const auto& case1 : sch1copy._cases) {
    for (const auto& case2 : sch2copy._cases) {
      InductionScheme::Case c;
      if (createMergedCase(case1, case2, combinedInductionTerms, c, var)) {
        resCases.push_back(c);
      }
    }
  }

  res.init(std::move(resCases));
  addBaseCases(res);
  if (!res.checkWellFoundedness()) {
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "[Induction] induction scheme is not well-founded: " << endl
        << res << endl << "combined from schemes: " << endl
        << "1: " << sch1 << endl << "2: " << sch2 << endl;
      env.endOutput();
    }
    return false;
  }

  return true;
}

void InductionSchemeFilter::filter(vvector<InductionScheme>& primary, vvector<InductionScheme>& secondary)
{
  CALL("InductionSchemeGenerator::filter");

  filter(primary);
  filter(secondary);

  // merge secondary schemes into primary ones if possible, remove the rest
  for (unsigned i = 0; i < secondary.size(); i++) {
    for (unsigned j = 0; j < primary.size(); j++) {
      auto& p = primary[j];
      auto& s = secondary[i];

      if (!beforeMergeCheck(p, s)) {
        continue;
      }

      InductionScheme merged;
      if (checkSubsumption(s, p)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] secondary induction scheme " << s
                    << " is subsumed by primary " << p << endl;
          env.endOutput();
        }
      } else if (checkSubsumption(p, s)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p
                    << " is subsumed by secondary " << s << endl;
          env.endOutput();
        }
        p = std::move(s);
      } else if (mergeSchemes(p, s, merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p
                    << " and secondary induction scheme " << s
                    << " are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        p = std::move(merged);
        break;
      }
    }
  }
  secondary.clear();
}

void InductionSchemeFilter::filter(vvector<InductionScheme>& schemes)
{
  CALL("InductionSchemeFilter::filter");

  for (unsigned i = 0; i < schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < schemes.size();) {

      if (!beforeMergeCheck(schemes[i], schemes[j])) {
        j++;
        continue;
      }

      InductionScheme merged;
      if (checkSubsumption(schemes[j], schemes[i])) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[j]
                    << " is subsumed by " << schemes[i] << endl;
          env.endOutput();
        }
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
      } else if (checkSubsumption(schemes[i], schemes[j])) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[i]
                    << " is subsumed by " << schemes[j] << endl;
          env.endOutput();
        }
        subsumed = true;
        break;
      } else if (mergeSchemes(schemes[j], schemes[i], merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction schemes " << schemes[j]
                    << " and " << schemes[i]
                    << "are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
        schemes[i] = merged;
        break;
      } else {
        j++;
      }
    }
    if (subsumed) {
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

void InductionSchemeFilter::filterComplex(vvector<InductionScheme>& schemes, const OccurrenceMap& occMap)
{
  for (unsigned i = 0; i < schemes.size();) {
    bool filter = false;
    for (const auto& c : schemes[i]._cases) {
      for (const auto& kv : c._step) {
        auto term = kv.first;
        if (env.signature->getFunction(term.term()->functor())->skolem()) {
          continue;
        }
        // filter out complex terms that contain
        // Skolem constants that are not exclusively
        // present in occurrences of this complex term
        // also filter out ones without Skolem constants
        unsigned occ = 0;
        for (const auto& kv : occMap) {
          if (kv.first.second == term) {
            occ += kv.second.num_bits();
          }
        }
        if (occ == 1) {
          filter = true;
          break;
        }
      }
      if (filter) {
        break;
      }
    }
    if (filter) {
      // cout << "scheme inducting on complex terms filtered out " << schemes[i].first << endl;
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

/**
 * Checks whether sch1 is subsumed by sch2 by the following criteria:
 * - all step cases of sch1 is a subterm of some step case of sch2
 *   up to variable renaming
 * - base cases are not checked since exhaustiveness of cases and
 *   containment of step cases implies containment of base cases too
 */
bool InductionSchemeFilter::checkSubsumption(const InductionScheme& sch1, const InductionScheme& sch2)
{
  CALL("checkSubsumption");

  if (sch1._inductionTerms != sch2._inductionTerms) {
    return false;
  }

  for (const auto& case1 : sch1._cases) {
    if (case1._recursiveCalls.empty()) {
      continue;
    }
    bool foundStep = false;
    for (const auto& case2 : sch2._cases) {
      // only check recursive cases
      if (case2._recursiveCalls.empty()) {
        continue;
      }

      if (case2.contains(case1)) {
        foundStep = true;
        break;
      }
    }
    if (!foundStep) {
      return false;
    }
  }
  return true;
}

} // Shell
