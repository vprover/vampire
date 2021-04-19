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

#include "Kernel/Clause.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Shell/TermAlgebra.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Signature.hpp"

#include "FunctionDefinitionDiscovery.hpp"

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

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch)
{
  if (!branch._recursiveCalls.empty()) {
    out << "(";
    unsigned n = 0;
    for (const auto& r : branch._recursiveCalls) {
      out << r;
      if (++n < branch._recursiveCalls.size()) {
        out << " & ";
      }
    }
    out << ") => ";
  }
  out << branch._header;
  return out;
}

bool InductionTemplate::findVarOrder(
  const vvector<vvector<VarType>>& relations,
  const vset<unsigned>& candidates,
  VarOrder& res)
{
  if (relations.empty()) {
    // add remaining candidates at end
    res.push_back(candidates);
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

bool InductionTemplate::checkWellDefinedness(vvector<vvector<TermList>>& missingCases)
{
  missingCases.clear();
  auto arity = _branches[0]._header.term()->arity();
  if (arity == 0) {
    return true;
  }
  if (_branches.empty()) {
    return false;
  }
  unsigned var = 0;
  vvector<vvector<TermList>> availableTermsEmpty;
  for (unsigned i = 0; i < arity; i++) {
    vvector<TermList> v;
    v.push_back(TermList(var++, false));
    availableTermsEmpty.push_back(v);
  }
  vvector<vvector<vvector<TermList>>> availableTermsLists;
  availableTermsLists.push_back(availableTermsEmpty);

  bool overdefined = false;
  for (auto& b : _branches) {
    vvector<vvector<vvector<TermList>>> nextAvailableTermsLists;
    Term::Iterator it(b._header.term());
    unsigned j = 0;
    while (it.hasNext()) {
      auto arg = it.next();
      bool excluded = false;
      if (arg.isTerm()) {
        auto tempLists = availableTermsLists;
        for (auto& availableTerms : tempLists) {
          if (TermAlgebra::excludeTermFromAvailables(availableTerms[j], arg, var)) {
            excluded = true;
          }
        }
        nextAvailableTermsLists.insert(nextAvailableTermsLists.end(),
          tempLists.begin(), tempLists.end());
      } else {
        for (const auto& availableTerms : availableTermsLists) {
          if (!availableTerms[j].empty()) {
            excluded = true;
            break;
          }
        }
      }
      if (!excluded) {
        overdefined = true;
      }
      j++;
    }
    availableTermsLists = nextAvailableTermsLists;
  }

  for (const auto& availableTerms : availableTermsLists) {
    bool valid = true;
    vvector<vvector<TermList>> argTuples(1);
    for (const auto& v : availableTerms) {
      if (v.empty()) {
        valid = false;
        break;
      }
      for (const auto& e : v) {
        vvector<vvector<TermList>> temp;
        for (auto a : argTuples) {
          a.push_back(e);
          temp.push_back(a);
        }
        argTuples = temp;
      }
    }
    if (valid) {
      missingCases.insert(missingCases.end(),
        argTuples.begin(), argTuples.end());
    }
  }
  return !overdefined && missingCases.empty();
}

void InductionTemplate::addMissingCases(const vvector<vvector<TermList>>& missingCases)
{
  auto mainTerm = _branches.begin()->_header.term();
  auto fn = mainTerm->functor();
  auto arity = mainTerm->arity();
  bool isPred = mainTerm->isLiteral();

  env.beginOutput();
  env.out() << "% Warning: adding missing cases ";
  for (const auto& m : missingCases) {
    Stack<TermList> args;
    ASS_EQ(m.size(),arity);
    for(const auto& arg : m) {
      args.push(arg);
    }
    TermList t;
    if (isPred) {
      t = TermList(Literal::create(static_cast<Literal*>(mainTerm), args.begin()));
    } else {
      t = TermList(Term::create(fn, arity, args.begin()));
    }
    env.out() << t << ", ";
    _branches.emplace_back(t);
  }
  env.out() << "to template " << *this << endl;
  env.endOutput();
}

bool InductionTemplate::Branch::contains(Branch other)
{
  if (!MatchingUtils::haveVariantArgs(_header.term(), other._header.term()))
  {
    return false;
  }
  for (auto recCall2 : other._recursiveCalls) {
    bool found = false;
    for (auto recCall1 : _recursiveCalls) {
      if (MatchingUtils::haveVariantArgs(recCall1.term(), recCall2.term()))
      {
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

bool InductionTemplate::checkUsefulness()
{
  CALL("InductionTemplate::checkUsefulness");

  // discard whenever:
  // (1) no r-descriptions or
  // (2) no terms in any argument positions or
  // (3) no recursive calls
  bool discard = true;
  for (auto& b : _branches) {
    Term::Iterator argIt(b._header.term());
    if (!b._recursiveCalls.empty()) {
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
    auto t = _branches.begin()->_header.term();
    if (env.options->showInduction()) {
      env.beginOutput();
      env.out() << "% Warning: template for "
                << (t->isLiteral() ? "predicate " : "function ")
                << (t->isLiteral() ? static_cast<Literal*>(t)->predicateName() : t->functionName())
                << " is discarded because it is not useful" << endl;
      env.endOutput();
    }
  }
  return !discard;
}

bool InductionTemplate::checkWellFoundedness()
{
  CALL("InductionTemplate::checkWellFoundedness");

  if (_branches.empty()) {
    return true;
  }

  // fill in bit vector of induction variables
  auto arity = _branches[0]._header.term()->arity();
  _inductionPositions = vvector<bool>(arity, false);
  vset<unsigned> candidatePositions;
  vvector<vvector<VarType>> relations;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      vvector<VarType> relation(arity, VarType::OTHER);
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(b._header.term());
      unsigned i = 0;
      while (argIt1.hasNext()) {
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        if (t1 == t2) {
          relation[i] = VarType::FIXED;
        } else if (t2.containsSubterm(t1)) {
          relation[i] = VarType::SUBTERM;
          candidatePositions.insert(i);
          _inductionPositions[i] = true;
        } else {
          candidatePositions.insert(i);
          _inductionPositions[i] = true;
        }
        i++;
      }
      relations.push_back(relation);
    }
  }
  _order.clear();
  return findVarOrder(relations, candidatePositions, _order);
}

void InductionTemplate::addBranch(vvector<TermList>&& recursiveCalls, TermList&& header)
{
  InductionTemplate::Branch branch(recursiveCalls, header);
  for (auto b : _branches) {
    // TODO(mhajdu): this should be checked the other way around as well
    if (b.contains(branch)) {
      return;
    }
  }
  _branches.emplace_back(branch);
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "Branches: ";
  unsigned n = 0;
  for (const auto& b : templ._branches) {
    out << b;
    if (++n < templ._branches.size()) {
      out << "; ";
    }
  }
  out << " with positions: (";
  auto arity = templ._branches[0]._header.term()->arity();
  for (unsigned i = 0; i < arity; i++) {
    if (templ._inductionPositions[i]) {
      out << "i";
    } else {
      out << "0";
    }
    if (i+1 < arity) {
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
  out << ")";
  return out;
}

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

void InductionPreprocessor::preprocessProblem(Problem& prb)
{
  CALL("InductionPreprocessor::preprocessProblem");

  // FunctionDefinitionDiscovery d;
  vmap<pair<unsigned, bool>, InductionTemplate> templates;
  UnitList::Iterator it(prb.units());
  while (it.hasNext()) {
    auto unit = it.next();
    if (!unit->isClause()){
      continue;
    }

    auto clause = unit->asClause();
    unsigned length = clause->length();
    if (!clause->containsFunctionDefinition()) {
      continue;
    }
    // first we find the only function
    // definition literal in the clause
    Literal* fndef = nullptr;
    for(unsigned i = 0; i < length; i++) {
      Literal* curr = (*clause)[i];
      if (clause->isFunctionDefinition(curr)) {
        ASS(!fndef);
        fndef = curr;
      }
    }

    if (fndef->isEquality()) {
      // if it is an equality the task is
      // to identify the lhs and collect any
      // recursive calls from the rhs
      auto rev = clause->isReversedFunctionDefinition(fndef);
      auto lhs = *fndef->nthArgument(rev ? 1 : 0);
      auto rhs = *fndef->nthArgument(rev ? 0 : 1);
      ASS(lhs.isTerm());

      auto fn = lhs.term()->functor();
      auto p = make_pair(fn, false);
      auto templIt = templates.find(p);
      if (templIt == templates.end()) {
        templIt = templates.insert(make_pair(p, InductionTemplate())).first;
      }

      vvector<TermList> recursiveCalls;
      processCase(fn, rhs, recursiveCalls);
      templIt->second.addBranch(std::move(recursiveCalls), std::move(lhs));
    } else {
      // otherwise we go once again through
      // the clause and look for other literals
      // with the same top-level functor
      auto functor = fndef->functor();
      auto p = make_pair(functor, true);
      auto templIt = templates.find(p);
      if (templIt == templates.end()) {
        templIt = templates.insert(make_pair(p, InductionTemplate())).first;
      }

      vvector<TermList> recursiveCalls;
      for(unsigned i = 0; i < length; i++) {
        Literal* curr = (*clause)[i];
        if (curr != fndef) {
          if (!curr->isEquality() && functor == curr->functor()) {
            recursiveCalls.push_back(TermList(curr));
          }
        }
      }
      // we unmake it, in saturation we do not process
      // predicate definitions differently (yet)
      clause->clearFunctionDefinitions();
      templIt->second.addBranch(std::move(recursiveCalls), std::move(TermList(fndef)));
    }

    // if (env.options->functionDefinitionDiscovery()) {
    //   d.findPossibleRecursiveDefinitions(formula);
    // }
  }
  for (const auto& kv : templates) {
    auto templ = kv.second;
    if (!templ.checkUsefulness()) {
      continue;
    }
    templ.checkWellFoundedness();
    vvector<vvector<TermList>> missingCases;
    if (!templ.checkWellDefinedness(missingCases) && !missingCases.empty()) {
      templ.addMissingCases(missingCases);
    }

    if(env.options->showInduction()){
      env.beginOutput();
      if (kv.first.second) {
        env.out() << "[Induction] predicate: " << env.signature->getPredicate(kv.first.first)->name() << endl;
      } else {
        env.out() << "[Induction] function: " << env.signature->getFunction(kv.first.first)->name() << endl;
      }
      env.out() << ", with induction template: " << templ << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(kv.first.first, kv.first.second, std::move(templ));
  }
  // d.addBestConfiguration();
}

} // Shell
