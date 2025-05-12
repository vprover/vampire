/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InductionTemplate.cpp
 * Implements class InductionTemplate.
 */

#include "InductionTemplate.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

using namespace std;

namespace Kernel {

template<typename S, typename T>
ostream& outputImplication(ostream& out, const Stack<S>& antecedent, const T& succeedent, bool outerParentheses = true)
{
  if (outerParentheses && antecedent.isNonEmpty()) {
    out << "(";
  }
  if (antecedent.size()>1) {
    out << "(";
  }
  for (unsigned i = 0; i < antecedent.size(); i++) {
    out << antecedent[i];
    if (i + 1 < antecedent.size()) {
      out << " & ";
    }
  }
  if (antecedent.size()>1) {
    out << ")";
  }
  if (antecedent.isNonEmpty()) {
    out << " => ";
  }
  out << succeedent;
  if (outerParentheses && antecedent.isNonEmpty()) {
    out << ")";
  }
  return out;
}

InductionUnit::InductionUnit(TermStack&& F_terms, LiteralStack&& conditions, VStack&& condUnivVars)
  : F_terms(F_terms), conditions(conditions), condUnivVars(condUnivVars)
{
  ASS(F_terms.isNonEmpty());
}

void InductionUnit::collectVariableSorts(const DHSet<unsigned>& sortVars, const TermStack& sorts, DHMap<unsigned,TermList>& varSorts) const
{
  ASS_EQ(sorts.size(), F_terms.size());
  for (unsigned i = 0; i < sorts.size(); i++) {
    auto t = F_terms[i];
    if (t.isVar()) {
      ASS(!sortVars.contains(t.var()));
      if (!varSorts.insert(t.var(), sorts[i])) {
        ASS_EQ(sorts[i], varSorts.get(t.var()));
      }
    } else {
      ASS_EQ(sorts[i], SortHelper::getResultSort(t.term()));
      SortHelper::collectVariableSorts(t.term(), varSorts);
    }
  }
  for (const auto& l : conditions) {
    SortHelper::collectVariableSorts(l, varSorts);
  }
}

ostream& operator<<(ostream& out, const InductionUnit& u) {
  stringstream str;
  str << "F[";
  for (unsigned i = 0; i < u.F_terms.size(); i++) {
    str << u.F_terms[i];
    if (i + 1 < u.F_terms.size()) {
      str << ",";
    }
  }
  str << "]";
  auto cond_strs = Stack<string>::fromIterator(
    iterTraits(u.conditions.iter()).map([](const auto& lit){ return lit->toString(); }));
  outputImplication(out, cond_strs, str.str());
  return out;
}

InductionCase::InductionCase(InductionUnit&& conclusion, Stack<InductionUnit>&& hypotheses, VStack&& hypUnivVars)
  : conclusion(conclusion), hypotheses(hypotheses), hypUnivVars(hypUnivVars)
{
  ASS(iterTraits(hypotheses.iter()).all([&](const auto& h){
    return h.F_terms.size() == conclusion.F_terms.size();
  }));
}

ostream& operator<<(ostream& out, const InductionCase& c) {
  outputImplication(out, c.hypotheses, c.conclusion);
  return out;
}

InductionTemplate::InductionTemplate(TermStack&& sorts, Stack<InductionCase>&& cases, InductionUnit&& conclusion, unsigned maxVar, InferenceRule rule)
  : sorts(sorts), cases(cases), conclusion(conclusion), maxVar(maxVar), rule(rule)
{
#if VDEBUG
  DHSet<unsigned> sortVars;
  for (const auto& s : sorts) {
    iterTraits(VariableIterator(s)).forEach([&](const auto& t) {
      sortVars.insert(t.var());
    });
  }

  // check sorts and vars
  DHMap<unsigned,TermList> varSorts;
  conclusion.collectVariableSorts(sortVars, sorts, varSorts);

  ASS(cases.isNonEmpty());
  for (const auto& c : cases) {
    DHMap<unsigned,TermList> caseVars;
    c.conclusion.collectVariableSorts(sortVars, sorts, caseVars);
    for (const auto& h : c.hypotheses) {
      h.collectVariableSorts(sortVars, sorts, caseVars);
    }
    iterTraits(caseVars.items()).forEach([&](const auto& kv) {
      ASS_REP(sortVars.contains(kv.first) || varSorts.insert(kv.first, kv.second), *this);
    });
  }
#endif
}

ostream& operator<<(ostream& out, const InductionTemplate& t) {
  outputImplication(out, t.cases, t.conclusion, /*outerParentheses=*/false);
  return out << " [" << ruleName(t.rule) << "]";
}

}
