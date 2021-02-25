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

TermList applySubstAndVarReplacement(TermList t, const RobSubstitution& subst, unsigned bank, VarReplacement& vr) {
  auto newTerm = subst.apply(t, bank);
  return applyVarReplacement(newTerm, vr);
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

bool createSingleRDescription(const RDescriptionInst& rdesc, const InductionScheme& other,
  const vset<TermList>& combinedInductionTerms, vvector<RDescriptionInst>& res, unsigned& var)
{
  // base cases are not considered here
  if (rdesc._recursiveCalls.empty()) {
    return false;
  }
  // create available terms for all induction terms
  // that are mapped to non-variable terms, the rest will
  // be created when needed
  vmap<TermList, vvector<TermList>> availableTermsInitial;
  for (const auto& kv : rdesc._step) {
    if (kv.second.isTerm()) {
      availableTermsInitial.insert(
        make_pair(kv.first, vvector<TermList>({ kv.second })));
    }
  }
  vvector<vmap<TermList, vvector<TermList>>> availableTermsLists({ availableTermsInitial });

  for (const auto& rdesc2 : other._rDescriptionInstances) {
    if (rdesc2._recursiveCalls.empty()) {
      continue;
    }
    vvector<vmap<TermList, vvector<TermList>>> nextAvailableTermsList;
    // the conditions given by the terms of rdesc2 are conjuncted,
    // so their negation will be a disjunction and we have to create
    // separate lists of available terms for each of them by distributivity 
    for (const auto& indTerm : combinedInductionTerms) {
      auto it2 = rdesc2._step.find(indTerm);
      if (it2 == rdesc2._step.end()) {
        // no condition
        continue;
      }

      auto t2 = it2->second;
      if (t2.isTerm()) {
        // copy the current lists
        auto tempLists = availableTermsLists;
        // for each of them, impose the restriction
        // on the available terms in that list
        for (auto& availableTerms : tempLists) {
          auto pIt = availableTerms.find(indTerm);
          if (pIt == availableTerms.end()) {
            // induction term was mapped to a variable in rdesc,
            // generate the available terms for it now
            pIt = availableTerms.insert(make_pair(
              indTerm,
              TermAlgebra::generateAvailableTerms(indTerm.term(), var))).first;
          }
          TermAlgebra::excludeTermFromAvailables(availableTerms.at(indTerm), t2, var);
        }
        nextAvailableTermsList.insert(nextAvailableTermsList.end(), tempLists.begin(), tempLists.end());
      }
    }
    // finally replace current lists with new ones
    availableTermsLists = nextAvailableTermsList;
  }

  // generate cross-product of available terms in result:
  // - each list contains available terms for induction terms
  // - any combination of these from the same list is valid 
  res.clear();
  for (const auto& availableTerms : availableTermsLists) {
    // initially we have only the original rdesc
    vvector<RDescriptionInst> rdescList({ rdesc });
    auto invalid = false;
    for (const auto& kv : availableTerms) {
      auto indTerm = kv.first;
      if (kv.second.empty()) {
        // no available terms, cross product is empty
        invalid = true;
        break;
      }
      vvector<RDescriptionInst> nextRdescList;
      for (const auto& p : kv.second) {
        for (auto rdesc : rdescList) { // intentionally copy rdesc here
          auto rIt = rdesc._step.find(indTerm);
          if (rIt == rdesc._step.end()) {
            rdesc._step.insert(make_pair(indTerm, p));
          } else {
            // we unify the term in rdesc with the available
            // term to get the substitution needed for
            // conditions and recursive calls
            DHMap<unsigned, unsigned> varMap;
            VarReplacement vr(varMap, var);
            RobSubstitution subst;
            ALWAYS(subst.unify(rIt->second, 0, p, 1));
            rIt->second = applySubstAndVarReplacement(rIt->second, subst, 0, vr);

            for (auto& recCall : rdesc._recursiveCalls) {
              auto recIt = recCall.find(kv.first);
              if (recIt != recCall.end()) {
                recIt->second = applySubstAndVarReplacement(recIt->second, subst, 0, vr);
              }
              // TODO(mhajdu): initially we had all induction terms in each
              // recursive call if it is present in the main substitution
              // but since this counts as explicitly strengthening the formula,
              // we do not want that yet
              // else {
              //   recCall.insert(make_pair(kv.first, TermList(var++, false)));
              // }
            }
          }
          nextRdescList.push_back(rdesc);
        }
      }
      rdescList = nextRdescList;
    }
    if (!invalid) {
      res.insert(res.end(), rdescList.begin(), rdescList.end());
    }
  }

  return true;
}

bool createMergedRDescription(const RDescriptionInst& rdesc1, const RDescriptionInst& rdesc2,
  const vset<TermList>& combinedInductionTerms, RDescriptionInst& res, unsigned& var)
{
  if (rdesc1._recursiveCalls.empty() || rdesc2._recursiveCalls.empty()) {
    return false;
  }
  vmap<TermList, TermList> step;
  vmap<TermList, RobSubstitutionSP> substs;
  vmap<TermList, DHMap<unsigned, unsigned>> varMaps;
  vmap<TermList, VarReplacement> varReplacements;
  for (const auto& indTerm : combinedInductionTerms) {
    auto it1 = rdesc1._step.find(indTerm);
    auto it2 = rdesc2._step.find(indTerm);
    ASS(it1 != rdesc1._step.end() || it2 != rdesc2._step.end());
    varMaps.insert(make_pair(indTerm, DHMap<unsigned, unsigned>()));
    VarReplacement vr(varMaps.at(indTerm), var);
    if (it1 != rdesc1._step.end() && it2 != rdesc2._step.end()) {
      auto t1 = it1->second;
      auto t2 = it2->second;
      RobSubstitutionSP subst(new RobSubstitution);
      if (!subst->unify(t1, 0, t2, 1)) {
        return false;
      }
      step.insert(make_pair(indTerm, applySubstAndVarReplacement(t1, *subst, 0, vr)));
      substs.insert(make_pair(indTerm, subst));
    } else if (it1 != rdesc1._step.end()) {
      step.insert(make_pair(indTerm, applyVarReplacement(it1->second, vr)));
    } else if (it2 != rdesc2._step.end()) {
      step.insert(make_pair(indTerm, applyVarReplacement(it2->second, vr)));
    }
    varReplacements.insert(make_pair(indTerm, vr));
  }
  vvector<vmap<TermList, TermList>> recCalls;
  for (const auto& recCall : rdesc1._recursiveCalls) {
    vmap<TermList, TermList> resRecCall;
    for (const auto& kv : recCall) {
      resRecCall.insert(make_pair(kv.first,
        (substs.count(kv.first)) ?
          applySubstAndVarReplacement(kv.second, *substs.at(kv.first), 0, varReplacements.at(kv.first)) :
          applyVarReplacement(kv.second, varReplacements.at(kv.first))));
    }
    recCalls.push_back(resRecCall);
  }
  for (const auto& recCall : rdesc2._recursiveCalls) {
    vmap<TermList, TermList> resRecCall;
    for (const auto& kv : recCall) {
      resRecCall.insert(make_pair(kv.first,
        (substs.count(kv.first)) ?
          applySubstAndVarReplacement(kv.second, *substs.at(kv.first), 1, varReplacements.at(kv.first)) :
          applyVarReplacement(kv.second, varReplacements.at(kv.first))));
    }
    recCalls.push_back(resRecCall);
  }
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

  res = RDescriptionInst(std::move(recCalls), std::move(step));
  return true;
}

void addBaseCases(InductionScheme& sch) {
  // here we do essentially the same as in createSingleRdescription,
  // only we do it on an initially empty RDescriptionInst and exclude
  // all other in the scheme
  unsigned var = sch._maxVar;
  vvector<vmap<TermList, vvector<TermList>>> availableTermsLists(1); // contains one empty map
  for (const auto& rdesc : sch._rDescriptionInstances) {
    vvector<vmap<TermList, vvector<TermList>>> nextAvailableTermsLists;
    for (const auto& kv : rdesc._step) {
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
        for (auto step : temp) { // intentionally copy rdesc here
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
    sch._rDescriptionInstances.emplace_back(std::move(emptyRecCalls), std::move(step));
  }
  sch._maxVar = var;
}

bool InductionSchemeFilter::mergeSchemes(const InductionScheme& sch1, const InductionScheme& sch2, InductionScheme& res) {
  // copy original schemes in case we fail and we modified them
  InductionScheme sch1copy = sch1;
  InductionScheme sch2copy = sch2.makeCopyWithVariablesShifted(sch1copy._maxVar+1);

  if (!includes(sch1._inductionTerms.begin(), sch1._inductionTerms.end(),
      sch2._inductionTerms.begin(), sch2._inductionTerms.end()) &&
      !includes(sch2._inductionTerms.begin(), sch2._inductionTerms.end(),
      sch1._inductionTerms.begin(), sch1._inductionTerms.end())) {
    return false;
  }
  vset<TermList> combinedInductionTerms = sch1._inductionTerms;
  combinedInductionTerms.insert(sch2._inductionTerms.begin(), sch2._inductionTerms.end());

  vvector<RDescriptionInst> resRdescs;
  unsigned var = 0;
  for (const auto& rdesc : sch1copy._rDescriptionInstances) {
    vvector<RDescriptionInst> inst;
    if (createSingleRDescription(rdesc, sch2copy, combinedInductionTerms, inst, var)) {
      resRdescs.insert(resRdescs.end(), inst.begin(), inst.end());
    }
  }
  for (const auto& rdesc : sch2copy._rDescriptionInstances) {
    vvector<RDescriptionInst> inst;
    if (createSingleRDescription(rdesc, sch1copy, combinedInductionTerms, inst, var)) {
      resRdescs.insert(resRdescs.end(), inst.begin(), inst.end());
    }
  }
  for (const auto& rdesc1 : sch1copy._rDescriptionInstances) {
    for (const auto& rdesc2 : sch2copy._rDescriptionInstances) {
      RDescriptionInst inst;
      if (createMergedRDescription(rdesc1, rdesc2, combinedInductionTerms, inst, var)) {
        resRdescs.push_back(inst);
      }
    }
  }

  res.init(std::move(resRdescs));
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

void mergeLitClausePairsInto(DHMap<Literal*, Clause*>* from, DHMap<Literal*, Clause*>* to)
{
  DHMap<Literal*, Clause*>::Iterator it(*from);
  while (it.hasNext()) {
    Literal* lit;
    Clause* cl;
    it.next(lit, cl);
    // if this is violated, a more complicated structure is needed
    ASS(!to->find(lit) || to->get(lit) == cl);
    to->insert(lit, cl);
  }
}

void InductionSchemeFilter::filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& primary,
  vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& secondary)
{
  CALL("InductionSchemeGenerator::filter");

  filter(primary);
  filter(secondary);

  // merge secondary schemes into primary ones if possible, remove the rest
  for (unsigned i = 0; i < secondary.size(); i++) {
    for (unsigned j = 0; j < primary.size(); j++) {
      auto& p = primary[j];
      auto& s = secondary[i];

      if (!beforeMergeCheck(p.first, s.first)) {
        continue;
      }

      InductionScheme merged;
      if (checkSubsumption(s.first, p.first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] secondary induction scheme " << s.first
                    << " is subsumed by primary " << p.first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(s.second, p.second);
      } else if (checkSubsumption(p.first, s.first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p.first
                    << " is subsumed by secondary " << s.first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(s.second, p.second);
        p.first = std::move(s.first);
      } else if (mergeSchemes(p.first, s.first, merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] primary induction scheme " << p.first
                    << " and secondary induction scheme " << s.first
                    << " are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        p.first = std::move(merged);
        mergeLitClausePairsInto(s.second, p.second);
        break;
      }
    }
  }
  for (auto& kv : secondary) {
    delete kv.second;
  }
  secondary.clear();
}

void InductionSchemeFilter::filter(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes)
{
  CALL("InductionSchemeFilter::filter");

  for (unsigned i = 0; i < schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < schemes.size();) {

      if (!beforeMergeCheck(schemes[i].first, schemes[j].first)) {
        j++;
        continue;
      }

      InductionScheme merged;
      if (checkSubsumption(schemes[j].first, schemes[i].first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[j].first
                    << " is subsumed by " << schemes[i].first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(schemes[j].second, schemes[i].second);
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
      } else if (checkSubsumption(schemes[i].first, schemes[j].first)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction scheme " << schemes[i].first
                    << " is subsumed by " << schemes[j].first << endl;
          env.endOutput();
        }
        mergeLitClausePairsInto(schemes[i].second, schemes[j].second);
        subsumed = true;
        break;
      } else if (mergeSchemes(schemes[j].first, schemes[i].first, merged)) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] induction schemes " << schemes[j].first
                    << " and " << schemes[i].first
                    << "are merged into:" << endl << merged << endl;
          env.endOutput();
        }
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
        schemes[i].first = merged;
        mergeLitClausePairsInto(schemes[j].second, schemes[i].second);
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

void InductionSchemeFilter::filterComplex(vvector<pair<InductionScheme, DHMap<Literal*, Clause*>*>>& schemes,
  DHMap<Literal*, DHMap<TermList, unsigned>*>* currOccMaps)
{
  for (unsigned i = 0; i < schemes.size();) {
    bool filter = false;
    for (const auto& rdesc : schemes[i].first._rDescriptionInstances) {
      for (const auto& kv : rdesc._step) {
        auto term = kv.first;
        if (isSkolem(term)) {
          continue;
        }
        // filter out complex terms that contain
        // Skolem constants that are not exclusively
        // present in occurrences of this complex term
        // also filter out ones without Skolem constants
        DHMap<Literal*, Clause*>::Iterator it(*schemes[i].second);
        unsigned occ = 0;
        while (it.hasNext()) {
          auto lit = it.nextKey();
          auto occmap = currOccMaps->get(lit);
          if (occmap->find(term)) {
            occ += occmap->get(term);
          }
        }
        if (occ == 1) {
          filter = true;
          break;
        }
        // while (it.hasNext()) {
        //   auto lit = it.nextKey();
        //   auto occ = currOccMaps->get(lit)->get(term);
        //   // if (occ == 1) {
        //   //   filter = true;
        //   //   break;
        //   // }
        //   SubtermIterator it(term.term());
        //   vmap<TermList,unsigned> skolemCount;
        //   while (it.hasNext()) {
        //     auto st = it.next();
        //     if (isSkolem(st)) {
        //       auto res = skolemCount.insert(make_pair(st, 0));
        //       res.first->second++;
        //     }
        //   }
        //   if (skolemCount.empty()) {
        //     filter = true;
        //   }
        //   for (const auto kv2 : skolemCount) {
        //     if (kv2.second*occ != currOccMaps->get(lit)->get(kv2.first)) {
        //       // cout << "literal " << *lit << " contains " << kv2.first << " outside of " << kv.first << endl;
        //       filter = true;
        //       break;
        //     }
        //   }
        //   if (filter) {
        //     break;
        //   }
        // }
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

  for (const auto& rdesc1 : sch1._rDescriptionInstances) {
    if (rdesc1._recursiveCalls.empty()) {
      continue;
    }
    bool foundStep = false;
    for (const auto& rdesc2 : sch2._rDescriptionInstances) {
      // only check recursive cases
      if (rdesc2._recursiveCalls.empty()) {
        continue;
      }

      if (rdesc2.contains(rdesc1)) {
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
