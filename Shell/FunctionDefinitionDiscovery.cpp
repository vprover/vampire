/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "FunctionDefinitionDiscovery.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "InductionPreprocessor.hpp"

using namespace Kernel;

namespace Shell {

bool isConstructorTerm(TermList t)
{
  CALL("isConstructorTerm");

  // vars are allowed even if they are
  // not of a term algebra sort
  if (t.isVar()) {
    return true;
  }

  if (t.term()->isSpecial()) {
    return false;
  }

  auto term = t.term();
  if (!env.signature->isTermAlgebraSort(SortHelper::getResultSort(term))
    || !isTermAlgebraCons(t)) {
    return false;
  }

  Term::Iterator it(term);
  while (it.hasNext()) {
    auto arg = it.next();
    if (!isConstructorTerm(arg)) {
      return false;
    }
  }
  return true;
}

bool isHeader(TermList t)
{
  CALL("isHeader");

  if (t.isVar()) {
    return false;
  }

  if (t.term()->isSpecial() || isTermAlgebraCons(t)) {
    return false;
  }

  Term::Iterator it(t.term());
  while (it.hasNext()) {
    auto arg = it.next();
    if (!isConstructorTerm(arg)) {
      return false;
    }
  }
  return true;
}

bool checkContains(const RDescription& rdesc1, const RDescription& rdesc2)
{
  RobSubstitutionSP subst(new RobSubstitution);
  // try to unify the step cases
  if (!subst->unify(rdesc2._step, 0, rdesc1._step, 1)) {
    return false;
  }
  auto t1 = subst->apply(rdesc1._step, 1);
  Renaming r1, r2;
  r1.normalizeVariables(rdesc1._step);
  r2.normalizeVariables(rdesc2._step);
  auto t2 = subst->apply(rdesc2._step, 0);
  if (t1 != r1.apply(rdesc1._step) || t2 != r2.apply(rdesc2._step)) {
    return false;
  }
  if (!rdesc1._conditions.empty() || !rdesc2._conditions.empty()) {
    return false;
  }
  for (const auto& recCall1 : rdesc1._recursiveCalls) {
    bool found = false;
    for (const auto& recCall2 : rdesc2._recursiveCalls) {
      const auto& r1 = subst->apply(recCall1, 1);
      const auto& r2 = subst->apply(recCall2, 0);
      if (r1 == r2) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

void FunctionDefinitionDiscovery::addBestConfiguration()
{
  CALL("FunctionDefinitionDiscovery::addBestConfiguration");

  auto n = foundFunctionDefinitions.size();
  vvector<vset<unsigned>> nonWellFounded(n);
  vvector<vset<unsigned>> nonWellDefined(n);
  vvector<vmap<unsigned, vvector<vvector<TermList>>>> missingCases(n);
  unsigned i = 0;
  for (auto& fndefs : foundFunctionDefinitions) {
    for (auto& kv : fndefs) {
      auto& rdescs = kv.second.first._rDescriptions;
      for (unsigned i = 0; i < rdescs.size(); i++) {
        for (unsigned j = i+1; j < rdescs.size();) {
          if (checkContains(rdescs[j], rdescs[i])) {
            rdescs[j] = rdescs.back();
            rdescs.pop_back();
          } else {
            j++;
          }
        }
      }

      if (!kv.second.first.checkWellFoundedness())
      {
        nonWellFounded[i].insert(kv.first);
      }
      ALWAYS(missingCases[i].insert(make_pair(kv.first, vvector<vvector<TermList>>())).second);
      if (!kv.second.first.checkWellDefinedness(missingCases[i].at(kv.first)))
      {
        nonWellDefined[i].insert(kv.first);
      }
    }
    i++;
  }
  // calculate score: non well-founded templates count more
  unsigned best = nonWellFounded[0].size() * 5 + nonWellDefined[0].size();
  unsigned best_i = 0;
  for (unsigned i = 1; i < n; i++) {
    auto curr = nonWellFounded[i].size() * 5 + nonWellDefined[i].size();
    if (curr < best) {
      best = curr;
      best_i = i;
    }
  }
  auto& fndefs = foundFunctionDefinitions[best_i];
  if (best > 0) {
    env.beginOutput();
    env.out() << "% Warning: all function orientations contain non well-founded"
      " or non well-defined sets, best score " << best << " with "
      << nonWellFounded[best_i].size() << " non well-founded and "
      << nonWellDefined[best_i].size() << " non well-defined " << endl;
    env.endOutput();
  }
  for (auto& kv : fndefs) {
    if (kv.second.first.checkUsefulness()) {
      if (nonWellDefined[best_i].count(kv.first)
        && missingCases[best_i].at(kv.first).size() > 0)
      {
        kv.second.first.addMissingCases(missingCases[best_i].at(kv.first));
      }
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] function definition has been discovered: "
                  << env.signature->functionName(kv.first) << endl;
        if (!nonWellFounded[best_i].count(kv.first)) {
          env.out() << " with induction template: " << kv.second.first << endl;
        }
        env.endOutput();
      }
      if (!nonWellFounded[best_i].count(kv.first)) {
        env.signature->addInductionTemplate(kv.first, false, std::move(kv.second.first));
      } else {
        env.beginOutput();
        env.out() << "% Warning: non-well-founded template is discarded: " << kv.second.first << endl;
        env.endOutput();
      }
      if (env.options->functionDefinitionRewriting()) {
        for (auto& kv2 : kv.second.second) {
          kv2.first->makeFunctionDefinition();
          kv2.first->resetFunctionOrientation();
          if (kv2.second) {
            kv2.first->reverseFunctionOrientation();
          }
        }
      }
    }
  }
  for (auto& kv : foundPredicateDefinitions) {
    if (kv.second.checkUsefulness()) {
      vvector<vvector<TermList>> missingCases;
      if (!kv.second.checkWellDefinedness(missingCases)
          && missingCases.size() > 0)
      {
        kv.second.addMissingCases(missingCases);
      }
      if (kv.second.checkWellFoundedness()) {
        if(env.options->showInduction()){
          env.beginOutput();
          env.out() << "[Induction] predicate definition has been discovered: "
                    << env.signature->predicateName(kv.first)
                    << ", with induction template: " << kv.second << endl;
          env.endOutput();
        }
        env.signature->addInductionTemplate(kv.first, true, std::move(kv.second));
      }
    }
  }
}

void FunctionDefinitionDiscovery::findPossibleRecursiveDefinitions(Formula* f, vvector<Formula*> conditions)
{
  CALL("FunctionDefinitionDiscovery::findPossibleRecursiveDefinitions");

  switch(f->connective()) {
    case LITERAL: {
      auto lit = f->literal();
      if (lit->isEquality()) {
        auto lhs = *lit->nthArgument(0);
        auto rhs = *lit->nthArgument(1);
        auto processFn = [this, conditions](TermList header, TermList body, InductionTemplate& templ) {
          if (!isHeader(header)) {
            return false;
          }
          InductionPreprocessor::processBody(body, header, conditions, templ);
          // we have to check that the found relations
          // are decreasing, e.g. f(c(x),c(y))=f(x,y)
          // is checked both ways but only one is decreasing
          return templ.checkWellFoundedness();
        };
        InductionTemplate tlhs;
        auto succlhs = processFn(lhs, rhs, tlhs) && lhs.containsAllVariablesOf(rhs);
        InductionTemplate trhs;
        auto succrhs = processFn(rhs, lhs, trhs) && rhs.containsAllVariablesOf(lhs);

        auto temp = foundFunctionDefinitions;
        if (succlhs || succrhs) {
          foundFunctionDefinitions.clear();
        }
        auto insertFn = [this, temp, lit](TermList t, InductionTemplate templ, bool reversed) {
          for (auto fndefs : temp) {
            auto it = fndefs.find(t.term()->functor());
            if (it == fndefs.end()) {
              vvector<pair<Literal*,bool>> v;
              auto p = make_pair(templ, vvector<pair<Literal*,bool>>());
              p.second.push_back(make_pair(lit, reversed));
              fndefs.insert(make_pair(t.term()->functor(), p));
            } else {
              it->second.first._rDescriptions.insert(
                it->second.first._rDescriptions.end(),
                templ._rDescriptions.begin(),
                templ._rDescriptions.end());
              it->second.second.push_back(make_pair(lit, reversed));
            }
            foundFunctionDefinitions.push_back(fndefs);
          }
        };
        if (succlhs)
        {
          insertFn(lhs, tlhs, false);
        }
        if (succrhs)
        {
          insertFn(rhs, trhs, true);
        }
        if(env.options->showInduction()){
          env.beginOutput();
          if (succlhs) {
            env.out() << "[Induction] Equality " << lhs << "=" << rhs << " is probably a function definition axiom" << endl;
          }
          if (succrhs) {
            env.out() << "[Induction] Equality " << rhs << "=" << lhs << " is probably a function definition axiom" << endl;
          }
          env.endOutput();
        }
      } else {
        if (isHeader(TermList(lit))) {
          if(env.options->showInduction()){
            env.beginOutput();
            env.out() << "[Induction] Literal " << *lit << " is probably a predicate definition axiom" << endl;
            env.endOutput();
          }
          auto it = foundPredicateDefinitions.find(lit->functor());
          if (it == foundPredicateDefinitions.end()) {
            InductionTemplate templ;
            templ._rDescriptions.emplace_back(TermList(lit), conditions);
            foundPredicateDefinitions.insert(make_pair(lit->functor(), std::move(templ)));
          } else {
            it->second._rDescriptions.emplace_back(TermList(lit), conditions);
          }
        }
      }
      break;
    }
    case AND: {
      FormulaList::Iterator it(f->args());
      while (it.hasNext()) {
        auto arg = it.next();
        findPossibleRecursiveDefinitions(arg, conditions);
      }
      break;
    }
    case IMP: {
      conditions.push_back(f->left());
      findPossibleRecursiveDefinitions(f->right(), conditions);
      break;
    }
    case FORALL: {
      findPossibleRecursiveDefinitions(f->qarg(), conditions);
      break;
    }
    case IFF: {
      auto lhs = f->left();
      auto rhs = f->right();
      auto processFn = [this, conditions](Formula* header, Formula* body, InductionTemplate& templ) {
        if (header->connective() != LITERAL) {
          return false;
        }
        auto lit = header->literal();
        if (lit->isEquality() || !isHeader(TermList(lit))) {
          return false;
        }
        InductionPreprocessor::processFormulaBody(body, lit, conditions, templ);
        // we have to check that the found relations
        // are decreasing, e.g. p(c(x),c(y))<=>p(x,y)
        // is checked both ways but only one is decreasing
        return templ.checkWellFoundedness();
      };
      InductionTemplate tlhs;
      auto succlhs = processFn(lhs, rhs, tlhs);
      InductionTemplate trhs;
      auto succrhs = processFn(rhs, lhs, trhs);
      if (succlhs && succrhs
        && lhs->literal()->functor() == rhs->literal()->functor())
      {
        // TODO(mhajdu): this can happen and only one can be correct,
        // deal with it by creating two sets of templates
        ASSERTION_VIOLATION;
      } else {
        auto mergeDefs = [this](Term* t, const InductionTemplate& templ) {
          auto it = foundPredicateDefinitions.find(t->functor());
          if (it == foundPredicateDefinitions.end()) {
            foundPredicateDefinitions.insert(make_pair(t->functor(), templ));
          } else {
            it->second._rDescriptions.insert(
              it->second._rDescriptions.end(),
              templ._rDescriptions.begin(),
              templ._rDescriptions.end());
          }
        };
        if (succlhs) {
          mergeDefs(lhs->literal(), tlhs);
        }
        if (succrhs) {
          mergeDefs(rhs->literal(), trhs);
        }
      }
      if(env.options->showInduction()){
        env.beginOutput();
        if (succlhs) {
          env.out() << "[Induction] Equivalence " << lhs << "<=>" << rhs << " is probably a predicate definition axiom" << endl;
        }
        if (succrhs) {
          env.out() << "[Induction] Equivalence " << rhs << "<=>" << lhs << " is probably a predicate definition axiom" << endl;
        }
        env.endOutput();
      }
      break;
    }
    case NOT: {
      if (f->uarg()->connective() == LITERAL) {
        findPossibleRecursiveDefinitions(f->uarg(), conditions);
      }
      break;
    }
    case OR:
    case XOR:
    case EXISTS:
    case BOOL_TERM:
    case FALSE:
    case TRUE:
    case NAME:
    case NOCONN: {
      break;
    }
  }
}

} // Shell
