/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionPreprocessor2.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Kernel/Clause.hpp"

// #include "FunctionDefinitionDiscovery.hpp"

using namespace Kernel;

namespace Shell {

void processCase(const unsigned fn, TermList body, vvector<TermList>& recursiveCalls)
{
  CALL("processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  // Check if this term is a recursive call, store it
  auto term = body.term();
  ASS(!term->isSpecial());
  if (term->functor() == fn) {
    recursiveCalls.push_back(body);
  }

  NonVariableIterator it(term);
  while (it.hasNext()) {
    auto n = it.next();
    processCase(fn, n, recursiveCalls);
  }
}

void InductionPreprocessor2::preprocessProblem(Problem& prb)
{
  CALL("InductionPreprocessor2::preprocessProblem");

  // FunctionDefinitionDiscovery d;
  vmap<unsigned, InductionTemplate> templates;
  UnitList::Iterator it(prb.units());
  while (it.hasNext()) {
    auto unit = it.next();
    if (!unit->isClause()){
      continue;
    }

    auto clause = unit->asClause();
    unsigned length = clause->length();
    for(unsigned i = 0; i < length; i++) {
      Literal* curr = (*clause)[i];
      if (clause->containsFunctionDefinition()) {
        if (clause->isFunctionDefinition(curr)) {
          ASS(curr->isEquality());

          auto rev = clause->isReversedFunctionDefinition(curr);
          auto lhs = *curr->nthArgument(rev ? 1 : 0);
          auto rhs = *curr->nthArgument(rev ? 0 : 1);
          ASS(lhs.isTerm());

          auto fn = lhs.term()->functor();
          auto templIt = templates.find(fn);
          if (templIt == templates.end()) {
            templIt = templates.insert(make_pair(fn, InductionTemplate())).first;
          }

          vvector<TermList> recursiveCalls;
          processCase(fn, rhs, recursiveCalls);
          templIt->second._branches.emplace_back(recursiveCalls, lhs);
        }
      }
    }

    // if (env.options->functionDefinitionDiscovery()) {
    //   d.findPossibleRecursiveDefinitions(formula);
    // }
  }
  for (const auto& kv : templates) {
    auto templ = kv.second;
    if (!templ.checkUsefulness()) {
      return;
    }
    templ.checkWellFoundedness();
    vvector<vvector<TermList>> missingCases;
    if (!templ.checkWellDefinedness(missingCases) && !missingCases.empty()) {
      templ.addMissingCases(missingCases);
    }

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] function: " << env.signature->getFunction(kv.first)->name() << endl
                << ", with induction template: " << templ << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(kv.first, false, std::move(templ));
  }
  // d.addBestConfiguration();
}

} // Shell
