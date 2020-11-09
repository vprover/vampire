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
  if (relations.empty() || candidates.empty()) {
    return true;
  }
  // Split original candidate sets into sets that change together
  // with a bool variable for each to denote whether the set changes in at
  // least one relation (otherwise the set is not a true candidate)
  vmap<vset<unsigned>, bool> candidateSets;
  candidateSets.insert(make_pair(candidates, false));
  for (const auto& r : relations) {
    vset<unsigned> subterm;
    vset<unsigned> fixed;
    for (int i = 0; i < r.size(); i++) {
      if (r[i] == VarType::FIXED) {
        fixed.insert(i);
      } else if (r[i] == VarType::SUBTERM) {
        subterm.insert(i);
      }
    }
    vmap<vset<unsigned>, bool> newCandidateSets;
    for (const auto& kv : candidateSets) {
      vset<unsigned> sti, fi;
      auto c = kv.first;
      // Take intersections of current simultaneously changing
      // or fixed sets with ones that change together in another
      // relation. The result will be non-empty sets which change
      // together or remain fixed together in all relations
      set_intersection(c.begin(), c.end(), subterm.begin(), subterm.end(), inserter(sti, sti.end()));
      set_intersection(c.begin(), c.end(), fixed.begin(), fixed.end(), inserter(fi, fi.end()));
      if (!sti.empty()) {
        newCandidateSets.insert(make_pair(sti, true)); // set changed variable to true
      }
      if (!fi.empty()) {
        newCandidateSets.insert(make_pair(fi, kv.second));
      }
    }
    candidateSets = newCandidateSets;
  }
  for (const auto& kv : candidateSets) {
    // only deal with sets that change in at least relation
    if (kv.second) {
      // The remaining relations are the ones where
      // the selected candidate sets are fixed, otherwise
      // the order is established by the selected set
      vvector<vvector<VarType>> remainingRelations;
      for (const auto r : relations) {
        // we can check only the first of the set
        // because they are all fixed in the same relations
        if (r[*kv.first.begin()] == VarType::FIXED) {
          remainingRelations.push_back(r);
        }
      }
      vset<unsigned> remainingCandidates;
      set_difference(candidates.begin(), candidates.end(),
        kv.first.begin(), kv.first.end(),
        inserter(remainingCandidates, remainingCandidates.end()));
      VarOrder temp = res;
      temp.push_back(kv.first);
      if (findVarOrder(remainingRelations, remainingCandidates, temp)) {
        res = temp;
        return true;
      }
    }
  }
  return false;
}

void InductionTemplate::postprocess()
{
  CALL("InductionTemplate::postprocess");

  ASS(!_rDescriptions.empty());
  _rDescriptions.shrink_to_fit();

  // fill in bit vector of induction variables
  auto arity = _rDescriptions[0]._step.term()->arity();
  _inductionVariables = vvector<bool>(arity, false);
  vset<unsigned> candidatePositions;
  vvector<vvector<VarType>> relations;
  for (auto& rdesc : _rDescriptions) {
    auto step = rdesc._step.term();
    for (auto& r : rdesc._recursiveCalls) {
      vvector<VarType> relation(arity, VarType::OTHER);
      Term::Iterator argIt1(r.term());
      Term::Iterator argIt2(step);
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
  VarOrder res;
  if (findVarOrder(relations, candidatePositions, res)) {
    _order = res;
    cout << "Found ordering of variables: (";
    for (const auto& r : res) {
      if (r.size() == 1) {
        cout << *r.begin() << ",";
      } else {
        cout << "{";
        for (const auto& v : r) {
          cout << v << ",";
        }
        cout << "},";
      }
    }
    cout << ")" << endl;
  } else {
    cout << "Could not find order for variables" << endl;
  }
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
  out << ")";
  return out;
}

void InductionPreprocessor::preprocess(Problem& prb)
{
  preprocess(prb.units());
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

    if (formula->connective() != Connective::LITERAL) {
      continue;
    }

    auto lit = formula->literal();
    if (!lit->isRecursiveDefinition()) {
      continue;
    }
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
    templ.postprocess();

    if(env.options->showInduction()){
      env.beginOutput();
      env.out() << "[Induction] recursive function: " << *lit << endl << ", with induction template: " << templ << endl;
      env.endOutput();
    }
    env.signature->addInductionTemplate(lhterm->functor(), isPred, std::move(templ));
  }
}

void InductionPreprocessor::processBody(TermList& body, TermList header, vvector<Formula*> conditions, InductionTemplate& templ)
{
  CALL("InductionPreprocessor::processBody");

  // Base case
  if (body.isVar()) {
    templ._rDescriptions.emplace_back(header, conditions);
    return;
  }
  // Recursive case
  auto term = body.term();
  if (!term->isSpecial() || term->isFormula()) {
    vvector<TermList> recursiveCalls;
    processCase(header.term()->functor(), body, recursiveCalls);
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

void InductionPreprocessor::processCase(const unsigned recFun, TermList& body, vvector<TermList>& recursiveCalls)
{
  CALL("InductionPreprocessor::processCase");

  // If we arrived at a variable, nothing to do
  if (!body.isTerm()) {
    return;
  }

  // Check if this term is a recursive call, store it
  auto term = body.term();
  if (term->functor() == recFun) {
    recursiveCalls.push_back(body);
  }

  // Otherwise recurse into the subterms/subformulas
  if (term->isFormula()) {
    auto formula = term->getSpecialData()->getFormula();
    switch (formula->connective()) {
      case LITERAL: {
        TermList lit(formula->literal());
        processCase(recFun, lit, recursiveCalls);
        break;
      }
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) {
          // TODO(mhajdu): maybe don't create a new Term here
          TermList ft(Term::createFormula(it.next()));
          processCase(recFun, ft, recursiveCalls);
        }
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
      processCase(recFun, n, recursiveCalls);
    }
  }
}

} // Shell
