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

bool InductionTemplate::Branch::contains(InductionTemplate::Branch other)
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
  for (const auto& p : _inductionPositions) {
    if (p) {
      discard = false;
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

  // fill in bit vector of induction variables
  auto arity = _branches[0]._header.term()->arity();
  _inductionPositions = vvector<bool>(arity, false);
  vset<unsigned> candidatePositions;
  vvector<pair<TermList, TermList>> relatedTerms;
  for (auto& b : _branches) {
    for (auto& r : b._recursiveCalls) {
      relatedTerms.push_back(make_pair(b._header, r));
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(b._header.term());
      unsigned i = 0;
      while (argIt1.hasNext()) {
        auto t1 = argIt1.next();
        auto t2 = argIt2.next();
        _inductionPositions[i] = _inductionPositions[i] || (t1 != t2);
        i++;
      }
    }
  }
  return InductionPreprocessor::checkWellFoundedness(relatedTerms);
}

void InductionTemplate::addBranch(vvector<TermList>&& recursiveCalls, TermList&& header)
{
  InductionTemplate::Branch branch(recursiveCalls, header);
  for (auto b : _branches) {
    if (b.contains(branch)) {
      return;
    }
  }
  for (unsigned i = 0; i < _branches.size();) {
    if (branch.contains(_branches[i])) {
      _branches[i] = _branches.back();
      _branches.pop_back();
    } else {
      i++;
    }
  }
  _branches.emplace_back(branch);
}

ostream& operator<<(ostream& out, const InductionTemplate& templ)
{
  out << "Branches: ";
  unsigned n = 0;
  for (const auto& b : templ.branches()) {
    out << b;
    if (++n < templ.branches().size()) {
      out << "; ";
    }
  }
  out << " with positions: (";
  auto arity = templ.branches()[0]._header.term()->arity();
  for (unsigned i = 0; i < arity; i++) {
    if (templ.inductionPositions()[i]) {
      out << "i";
    } else {
      out << "0";
    }
    if (i+1 < arity) {
      out << ",";
    }
  }
  out << ")";
  return out;
}

void InductionPreprocessor::processCase(const unsigned fn, TermList body, vvector<TermList>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  NonVariableIterator it(body.term(), true);
  while (it.hasNext()) {
    auto st = it.next();
    if (st.term()->functor() == fn) {
      recursiveCalls.push_back(st);
    }
  }
}

void InductionPreprocessor::preprocessProblem(Problem& prb)
{
  CALL("InductionPreprocessor::preprocessProblem");

  FunctionDefinitionDiscovery d;
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
      if (env.options->functionDefinitionDiscovery()) {
        d.findPossibleDefinitions(clause);
      }
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
  }
  for (const auto& kv : templates) {
    auto templ = kv.second;
    if (!templ.checkWellFoundedness()) {
      env.beginOutput();
      env.out() << "% Warning: " << templ << " is not well founded" << endl;
      env.endOutput();
      continue;
    }
    if (!templ.checkUsefulness()) {
      continue;
    }
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
  d.addBestConfiguration();
}

bool checkWellFoundednessHelper(const vvector<pair<TermList,TermList>>& relatedTerms,
  const vset<unsigned>& indices, const vset<unsigned>& positions)
{
  if (indices.empty()) {
    return true;
  }
  if (positions.empty()) {
    return false;
  }
  ASS(relatedTerms[0].first.isTerm());
  for (const auto& p : positions) {
    vset<unsigned> newInd;
    bool canOrder = true;
    for (const auto& i : indices) {
      auto arg1 = *relatedTerms[i].first.term()->nthArgument(p);
      auto arg2 = *relatedTerms[i].second.term()->nthArgument(p);
      if (arg1 == arg2) {
        newInd.insert(i);
      } else if (!arg1.containsSubterm(arg2)) {
        canOrder = false;
        break;
      }
    }
    if (canOrder) {
      auto newPos = positions;
      newPos.erase(p);
      if (checkWellFoundednessHelper(relatedTerms, newInd, newPos)) {
        return true;
      }
    }
  }
  return false;
}

bool InductionPreprocessor::checkWellFoundedness(const vvector<pair<TermList,TermList>>& relatedTerms)
{
  if (relatedTerms.empty()) {
    return true;
  }
  auto t = relatedTerms[0].first.term();
  bool isFun = !t->isLiteral();
  auto fn = t->functor();
  auto arity = t->arity();
  OperatorType* type;
  if (isFun) {
    type = env.signature->getFunction(fn)->fnType();
  } else {
    type = env.signature->getPredicate(fn)->predType();
  }
  vset<unsigned> positions;
  for (unsigned i = 0; i < arity; i++) {
    if (env.signature->isTermAlgebraSort(type->arg(i))) {
      positions.insert(i);
    }
  }
#if VDEBUG
  for (const auto& kv : relatedTerms) {
    ASS(kv.first.isTerm() && kv.first.term()->functor() == fn &&
      kv.second.isTerm() && kv.second.term()->functor() == fn);
  }
#endif
  vset<unsigned> indices;
  for (unsigned i = 0; i < relatedTerms.size(); i++) {
    indices.insert(i);
  }
  return checkWellFoundednessHelper(relatedTerms, indices, positions);
}

} // Shell
