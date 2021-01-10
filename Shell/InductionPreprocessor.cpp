/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionPreprocessor.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Renaming.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

using namespace Kernel;

namespace Shell {

bool isTermAlgebraCons(TermList t)
{
  CALL("isTermAlgebraCons");

  if (t.isVar()) {
    return false;
  }
  auto func = t.term()->functor();
  auto symb = t.term()->isLiteral() ? env.signature->getPredicate(func) : env.signature->getFunction(func);
  return symb->termAlgebraCons();
}

bool isConstructorTerm(TermList t)
{
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

TermList TermListReplacement::transformSubterm(TermList trm)
{
  CALL("TermListReplacement::transformSubterm");

  if(trm.isVar() && _o.isVar() && trm.var() == _o.var()) {
    return _r;
  }

  if(trm.isTerm() && _o.isTerm() && trm.term()==_o.term()){
    return _r;
  }
  return trm;
}

ostream& operator<<(ostream& out, const RDescription& rdesc)
{
  unsigned n = 0;
  if (!rdesc._conditions.empty()) {
    out << "(";
    for (const auto& c : rdesc._conditions) {
      out << *c;
      if (++n < rdesc._conditions.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  if (!rdesc._recursiveCalls.empty()) {
    out << "(";
    n = 0;
    for (const auto& r : rdesc._recursiveCalls) {
      out << r;
      if (++n < rdesc._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << rdesc._step;
  return out;
}

bool InductionTemplate::findVarOrder(
  const vvector<vvector<VarType>>& relations,
  vset<unsigned>& candidates,
  VarOrder& res)
{
  if (relations.empty()) {
    return true;
  }
  if (candidates.empty()) {
    return false;
  }
  // Split original candidate sets into sets that change together
  // with a bool variable for each to denote whether the set changes in at
  // least one relation (otherwise the set is not a true candidate)
  vset<vset<unsigned>> candidateSets;
  candidateSets.insert(candidates);
  for (const auto& r : relations) {
    vset<unsigned> subterm;
    vset<unsigned> fixed;
    for (unsigned i = 0; i < r.size(); i++) {
      if (r[i] == VarType::FIXED) {
        fixed.insert(i);
      } else if (r[i] == VarType::SUBTERM) {
        subterm.insert(i);
      }
    }
    vset<vset<unsigned>> newCandidateSets;
    for (const auto& c : candidateSets) {
      vset<unsigned> sti, fi;
      // Take intersections of current simultaneously changing
      // or fixed sets with ones that change together in another
      // relation. The result will be non-empty sets which change
      // together or remain fixed together in all relations
      set_intersection(c.begin(), c.end(), subterm.begin(), subterm.end(), inserter(sti, sti.end()));
      set_intersection(c.begin(), c.end(), fixed.begin(), fixed.end(), inserter(fi, fi.end()));
      if (!sti.empty()) {
        newCandidateSets.insert(sti); // set changed variable to true
      }
      if (!fi.empty()) {
        newCandidateSets.insert(fi);
      }
    }
    candidateSets = newCandidateSets;
  }
  for (const auto& c : candidateSets) {
    // The remaining relations are the ones where
    // the selected candidate sets are fixed, otherwise
    // the order is established by the selected set
    vvector<vvector<VarType>> remainingRelations;
    for (const auto r : relations) {
      // we can check only the first of the set
      // because they are all fixed in the same relations
      if (r[*c.begin()] == VarType::FIXED) {
        remainingRelations.push_back(r);
      }
    }
    vset<unsigned> remainingCandidates;
    set_difference(candidates.begin(), candidates.end(),
      c.begin(), c.end(),
      inserter(remainingCandidates, remainingCandidates.end()));
    VarOrder temp = res;
    temp.push_back(c);
    if (findVarOrder(remainingRelations, remainingCandidates, temp)) {
      res = temp;
      return true;
    }
  }
  return false;
}

bool InductionTemplate::checkWellDefinedness()
{
  unsigned var = 0;
  vvector<vvector<TermList>> availableTermsEmpty;
  for (unsigned i = 0; i < _inductionVariables.size(); i++) {
    vvector<TermList> v;
    v.push_back(TermList(var++, false));
    availableTermsEmpty.push_back(v);
  }
  vvector<vvector<vvector<TermList>>> availableTermsLists;
  availableTermsLists.push_back(availableTermsEmpty);

  for (auto& rdesc : _rDescriptions) {
    vvector<vvector<vvector<TermList>>> nextAvailableTermsLists;
    Term::Iterator it(rdesc._step.term());
    unsigned j = 0;
    while (it.hasNext()) {
      auto arg = it.next();
      if (arg.isTerm()) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          if (!TermAlgebra::excludeTermFromAvailables(availableTerms[j], arg, var) && rdesc._conditions.empty()) {
            return false;
          }
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      } else {
        for (const auto& availableTerms : availableTermsLists) {
          if ((availableTerms[j].size() != 1 || availableTerms[j][0].isTerm()) && rdesc._conditions.empty()) {
            return false;
          }
        }
      }
      j++;
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  for (const auto& availableTerms : availableTermsLists) {
    bool valid = true;
    vvector<TermList> validArgs;
    for (const auto& v : availableTerms) {
      if (v.empty()) {
        valid = false;
        break;
      }
      validArgs.push_back(*v.begin());
    }
    if (valid) {
      if (env.options->showInduction()) {
        env.beginOutput();
        auto t = _rDescriptions.begin()->_step.term();
        env.out() << "[Induction] could not determine well-definedness for "
                  << (t->isLiteral() ? "predicate " : "function ")
                  << (t->isLiteral() ? static_cast<Literal*>(t)->predicateName() : t->functionName())
                  << " with template " << *this << " because it is not defined on argument combination ";
        for (const auto& v : validArgs) {
          env.out() << v << ", ";
        }
        env.out() << endl;
        env.endOutput();
      }
      return false;
    }
  }

  for (const auto& rdesc : _rDescriptions) {
    if (rdesc._conditions.empty()) {
      continue;
    }

    // we don't check any conditions more
    // complex than a single literal
    if (rdesc._conditions.size() > 1) {
      return false;
    }

    auto f1 = rdesc._conditions[0];
    const bool negation = f1->connective() == NOT;
    if (negation) {
      f1 = f1->uarg();
    }
    if (f1->connective() != LITERAL) {
      return false;
    }
    auto l1 = f1->literal();

    bool foundNeg = false;
    for (const auto& rdesc2 : _rDescriptions) {
      if (rdesc2._step != rdesc._step || rdesc2._conditions.size() != 1) {
        continue;
      }
      auto f2 = rdesc2._conditions[0];
      const bool negation2 = f2->connective() == NOT;
      if (negation2) {
        f2 = f2->uarg();
      }
      if (f2->connective() != LITERAL) {
        continue;
      }
      auto l2 = f2->literal();
      if (l1->isEquality() != l2->isEquality()) {
        continue;
      }
      if (negation == negation2 && l1->isPositive() == l2->isPositive()) {
        continue;
      }
      if (l1->nthArgument(0) != l2->nthArgument(0)) {
        continue;
      }
      if (l1->isEquality() && l1->nthArgument(1) != l2->nthArgument(1)) {
        continue;
      }
      foundNeg = true;
      break;
    }
    if (!foundNeg) {
      return false;
    }
  }

  return true;
}


bool InductionTemplate::checkUsefulness()
{
  CALL("InductionTemplate::checkUsefulness");

  // discard whenever:
  // (1) no r-descriptions or
  // (2) no terms in any argument positions or
  // (3) no recursive calls
  bool discard = true;
  for (auto& rdesc : _rDescriptions) {
    Term::Iterator argIt(rdesc._step.term());
    if (!rdesc._recursiveCalls.empty()) {
      discard = false;
    }
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (arg.isTerm()) {
        discard = false;
      }
    }
  }
  if (discard) {
    auto t = _rDescriptions.begin()->_step.term();
    env.beginOutput();
    env.out() << "% Warning: template for "
              << (t->isLiteral() ? "predicate " : "function ")
              << (t->isLiteral() ? static_cast<Literal*>(t)->predicateName() : t->functionName())
              << " is discarded because it is not useful" << endl;
    env.endOutput();
  }
  return !discard;
}

bool InductionTemplate::checkWellFoundedness()
{
  CALL("InductionTemplate::checkWellFoundedness");

  if (_rDescriptions.empty()) {
    return true;
  }

  // fill in bit vector of induction variables
  auto arity = _rDescriptions[0]._step.term()->arity();
  _inductionVariables = vvector<bool>(arity, false);
  vset<unsigned> candidatePositions;
  vvector<vvector<VarType>> relations;
  for (auto& rdesc : _rDescriptions) {
    for (auto& r : rdesc._recursiveCalls) {
      vvector<VarType> relation(arity, VarType::OTHER);
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(rdesc._step.term());
      unsigned i = 0;
      while (argIt1.hasNext()) {
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 == t2) {
          relation[i] = VarType::FIXED;
        } else if (t2.containsSubterm(t1)) {
          relation[i] = VarType::SUBTERM;
          candidatePositions.insert(i);
          _inductionVariables[i] = true;
        } else {
          candidatePositions.insert(i);
        }
        i++;
      }
      relations.push_back(relation);
    }
  }
  _order.clear();
  return findVarOrder(relations, candidatePositions, _order);
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "RDescriptions: ";
  unsigned n = 0;
  for (const auto& rdesc : templ._rDescriptions) {
    out << rdesc;
    if (++n < templ._rDescriptions.size()) {
      out << "; ";
    }
  }
  n = 0;
  out << " with inductive positions: (";
  for (const auto& b : templ._inductionVariables) {
    out << Int::toString(b);
    if (++n < templ._inductionVariables.size()) {
      out << ",";
    }
  }
  out << ") and variable order (";
  for (const auto& r : templ._order) {
    if (r.size() == 1) {
      out << *r.begin() << ",";
    } else {
      out << "{";
      for (const auto& v : r) {
        out << v << ",";
      }
      out << "},";
    }
  }
  out << ")" << endl;
  return out;
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

void InductionPreprocessor::preprocess(Problem& prb)
{
  // add empty set of templates
  foundFunctionDefinitions.emplace_back();
  preprocess(prb.units());
  vvector<unsigned> viableSets;
  vvector<unsigned> wellFoundedSets;
  unsigned i = 0;
  for (auto& fndefs : foundFunctionDefinitions) {
    bool viable = true;
    bool wellFounded = true;
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
        wellFounded = false;
        viable = false;
        break;
      }
      if (!kv.second.first.checkWellDefinedness())
      {
        viable = false;
      }
    }
    if (wellFounded) {
      wellFoundedSets.push_back(i);
    }
    if (viable) {
      viableSets.push_back(i);
    }
    i++;
  }
  ALWAYS(wellFoundedSets.size() > 1);
  auto& fndefs = foundFunctionDefinitions[wellFoundedSets[0]];
  if (viableSets.size() > 1) {
    fndefs = foundFunctionDefinitions[viableSets[0]];
  }
  for (auto& kv : fndefs) {
    if (kv.second.first.checkUsefulness()) {
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] recursive function definition has been discovered: "
                  << env.signature->functionName(kv.first)
                  << ", with induction template: " << kv.second.first << endl;
        env.endOutput();
      }
      env.signature->addInductionTemplate(kv.first, false, std::move(kv.second.first));
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
    if (env.signature->hasInductionTemplate(kv.first, true)) {
      env.beginOutput();
      env.out() << "% Warning: predicate definition already found for "
                << env.signature->predicateName(kv.first) << endl;
      env.endOutput();
      continue;
    }
    if (kv.second.checkWellFoundedness()
        && kv.second.checkWellDefinedness()
        && kv.second.checkUsefulness()) {
      if(env.options->showInduction()){
        env.beginOutput();
        env.out() << "[Induction] recursive predicate definition has been discovered: "
                  << env.signature->predicateName(kv.first)
                  << ", with induction template: " << kv.second << endl;
        env.endOutput();
      }
      env.signature->addInductionTemplate(kv.first, true, std::move(kv.second));
    } else {
      env.beginOutput();
      env.out() << "% Warning: could not determine predicate definition "
                << env.signature->predicateName(kv.first) << endl;
      env.endOutput();
    }
  }
}

void InductionPreprocessor::preprocess(UnitList* units)
{
  CALL("InductionPreprocessor::preprocess");

  UnitList::Iterator it(units);
  while (it.hasNext()) {
    auto unit = it.next();
    if (unit->isClause()){
      continue;
    }

    auto formula = unit->getFormula();
    while (formula->connective() == Connective::FORALL) {
      formula = formula->qarg();
    }

    if (formula->connective() == Connective::LITERAL
        && formula->literal()->isFunctionDefinition()) {
      parseRecursiveDefinition(formula->literal());
    } else {
      findPossibleRecursiveDefinitions(formula, vvector<Formula*>());
    }
  }
}

void InductionPreprocessor::parseRecursiveDefinition(Literal* lit)
{
  auto lhs = lit->nthArgument(0);
  auto rhs = lit->nthArgument(1);
  auto lhterm = lhs->term();
  bool isPred = lhterm->isFormula();
  if (isPred) {
    lhterm = lhterm->getSpecialData()->getFormula()->literal();
  }

  InductionTemplate templ;
  TermList term(lhterm);
  processBody(*rhs, term, vvector<Formula*>(), templ);
  if (!templ.checkWellFoundedness()
      || !templ.checkWellDefinedness()
      || !templ.checkUsefulness()) {
    return;
  }

  if(env.options->showInduction()){
    env.beginOutput();
    env.out() << "[Induction] recursive function: " << *lit << endl << ", with induction template: " << templ << endl;
    env.endOutput();
  }
  env.signature->addInductionTemplate(lhterm->functor(), isPred, std::move(templ));
}

void InductionPreprocessor::findPossibleRecursiveDefinitions(Formula* f, vvector<Formula*> conditions)
{
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
          processBody(body, header, conditions, templ);
          // we have to check that the found relations
          // are decreasing, e.g. f(c(x),c(y))=f(x,y)
          // is checked both ways but only one is decreasing
          return templ.checkWellFoundedness();
        };
        InductionTemplate tlhs;
        auto succlhs = processFn(lhs, rhs, tlhs);
        InductionTemplate trhs;
        auto succrhs = processFn(rhs, lhs, trhs);

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
        processFormulaBody(body, lit, conditions, templ);
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

void InductionPreprocessor::processFormulaBody(Formula* body, Literal* header, vvector<Formula*> conditions, InductionTemplate& templ)
{
  switch(body->connective()) {
    case LITERAL: {
      auto lit = body->literal();
      vvector<TermList> recCalls;
      if (lit->isEquality()) {
        processCase(header->functor(), header->isFormula(), *lit->nthArgument(0), recCalls);
        processCase(header->functor(), header->isFormula(), *lit->nthArgument(1), recCalls);
      } else {
        processCase(header->functor(), header->isFormula(), TermList(lit), recCalls);
      }
      templ._rDescriptions.emplace_back(recCalls, TermList(header), conditions);
      break;
    }
    case BOOL_TERM: {
      vvector<TermList> recCalls;
      processCase(header->functor(), header->isFormula(), body->getBooleanTerm(), recCalls);
      templ._rDescriptions.emplace_back(recCalls, TermList(header), conditions);
      break;
    }
    case AND:
    case OR: {
      FormulaList::Iterator it(body->args());
      while (it.hasNext()) {
        auto arg = it.next();
        processFormulaBody(arg, header, conditions, templ);
      }
      break;
    }
    case FALSE:
    case TRUE: {
      templ._rDescriptions.emplace_back(TermList(header), conditions);
      break;
    }
    case NOT: {
      processFormulaBody(body->uarg(), header, conditions, templ);
      break;
    }
    case IMP:
    case IFF:
    case XOR: {
      processFormulaBody(body->left(), header, conditions, templ);
      processFormulaBody(body->right(), header, conditions, templ);
      break;
    }
    case FORALL:
    case EXISTS:
    case NAME:
    case NOCONN: {
      break;
    }
  }
}

void InductionPreprocessor::processBody(TermList body, TermList header, vvector<Formula*> conditions, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processBody");

  // Base case
  if (body.isVar()) {
    templ._rDescriptions.emplace_back(header, conditions);
    return;
  }
  // Possibly recursive case
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    vvector<TermList> recursiveCalls;
    processCase(header.term()->functor(), header.term()->isFormula(), body, recursiveCalls);
    templ._rDescriptions.emplace_back(recursiveCalls, header, conditions);
    return;
  }
  // TODO(mhajdu): Here there can be other constructs e.g. ITE, process them
  auto sd = term->getSpecialData();
  if (term->isMatch())
  {
    auto matchedVar = term->nthArgument(0)->var();

    for (unsigned i = 1; i < term->arity(); i+=2) {
      auto pattern = term->nthArgument(i);
      auto matchBody = term->nthArgument(i+1);
      // We replace the matched variable with
      // the pattern in the header and recurse
      TermListReplacement tr(TermList(matchedVar,false), *pattern);
      TermList t(tr.transform(header.term()));
      auto cond = conditions;
      for (auto& c : cond) {
        c = tr.transform(c);
      }
      processBody(*matchBody, t, cond, templ);
    }
  }
  else if (term->isITE())
  {
    auto cond1 = conditions;
    auto cond2 = conditions;
    cond1.push_back(sd->getCondition());
    cond2.push_back(new NegatedFormula(sd->getCondition()));
    processBody(*term->nthArgument(0), header, cond1, templ);
    processBody(*term->nthArgument(1), header, cond2, templ);
  }
}

void InductionPreprocessor::processCase(const unsigned recFun, const bool isPred, TermList body, vvector<TermList>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  // Check if this term is a recursive call, store it
  auto term = body.term();
  if (term->functor() == recFun && isPred == term->isFormula()) {
    recursiveCalls.push_back(body);
  }

  // Otherwise recurse into the subterms/subformulas
  if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processCase(recFun, isPred, lit, recursiveCalls);
        break;
      }
      case BOOL_TERM: {
        processCase(recFun, isPred, formula->getBooleanTerm(), recursiveCalls);
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) {
          // TODO(mhajdu): maybe don't create a new Term here
          TermList ft(Term::createFormula(it.next()));
          processCase(recFun, isPred, ft, recursiveCalls);
        }
        break;
      }
      case IFF:
      case XOR:
      case IMP: {
        break;
      }
      case TRUE:
      case FALSE: {
        break;
      }
#if VDEBUG
      default:
        ASSERTION_VIOLATION;
#endif
    }
  } else {
    Term::Iterator it(term);
    while (it.hasNext()) {
      auto n = it.next();
      processCase(recFun, isPred, n, recursiveCalls);
    }
  }
}

} // Shell
