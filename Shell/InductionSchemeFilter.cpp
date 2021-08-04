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
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

using namespace Kernel;

namespace Shell {

void InductionSchemeFilter::filter(vvector<InductionScheme>& schemes, const OccurrenceMap& actOccMaps)
{
  CALL("InductionSchemeFilter::filter");

  static const bool filterC = env.options->inductionOnComplexTermsHeuristic();
  if (filterC) {
    filterComplex(schemes, actOccMaps);
  }

  for (unsigned i = 0; i < schemes.size();) {
    bool subsumed = false;
    for (unsigned j = i+1; j < schemes.size();) {

      if (checkContainment(schemes[j], schemes[i])) {
        schemes[j] = std::move(schemes.back());
        schemes.pop_back();
      }
      else if (checkContainment(schemes[i], schemes[j])) {
        subsumed = true;
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
    for (const auto& kv : schemes[i].inductionTerms()) {
      if (env.signature->getFunction(kv.first->functor())->skolem()) {
        continue;
      }
      unsigned occ = 0;
      for (const auto& kv2 : occMap._m) {
        if (kv2.first.second == kv.first) {
          occ += kv2.second.num_bits();
        }
      }
      if (occ == 1) {
        filter = true;
        break;
      }
    }
    if (filter) {
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "scheme inducting on complex terms filtered out " << schemes[i] << endl;
        env.endOutput();
      }
      schemes[i] = std::move(schemes.back());
      schemes.pop_back();
    } else {
      i++;
    }
  }
}

/**
 * Checks whether all cases of sch1 are contained by some case of sch2
 */
bool InductionSchemeFilter::checkContainment(const InductionScheme& sch1, const InductionScheme& sch2)
{
  CALL("InductionSchemeFilter::checkContainment");

  if (sch1.inductionTerms() != sch2.inductionTerms()) {
    return false;
  }

  for (const auto& case1 : sch1.cases()) {
    if (case1._recursiveCalls.empty()) {
      continue;
    }
    bool foundStep = false;
    for (const auto& case2 : sch2.cases()) {
      if (case2._recursiveCalls.empty()) {
        continue;
      }

      if (case2.contains(case1, sch1.inductionTerms(), sch2.inductionTerms())) {
        foundStep = true;
        break;
      }
    }
    if (!foundStep) {
      return false;
    }
  }
  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] induction scheme " << sch1
              << " is subsumed by " << sch2 << endl;
    env.endOutput();
  }
  return true;
}

} // Shell
