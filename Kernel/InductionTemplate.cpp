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

InductionUnit::InductionUnit(TermStack&& F_terms, LiteralStack&& conditions)
  : F_terms(F_terms), conditions(conditions)
{
  ASS(F_terms.isNonEmpty());
  // check that all variables in conditions are in F_terms
  ASS(iterTraits(conditions.iter()).all([&](const auto& lit) {
    return iterTraits(VariableIterator(lit)).all([&](const auto& t) {
      return iterTraits(F_terms.iter()).any([&](const auto& Ft) {
        return Ft.containsSubterm(t);
      });
    });
  }));
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

InductionCase::InductionCase(InductionUnit&& conclusion, Stack<InductionUnit>&& hypotheses)
  : conclusion(conclusion), hypotheses(hypotheses)
{
  ASS(iterTraits(hypotheses.iter()).all([&](const auto& h){
    return h.F_terms.size() == conclusion.F_terms.size();
  }));
}

ostream& operator<<(ostream& out, const InductionCase& c) {
  outputImplication(out, c.hypotheses, c.conclusion);
  return out;
}

InductionTemplate::InductionTemplate(Stack<InductionCase>&& cases, InductionUnit&& conclusion, InferenceRule rule)
  : cases(cases), conclusion(conclusion), rule(rule)
{
  ASS(cases.isNonEmpty());
  ASS_REP(iterTraits(cases.iter()).all([&](const auto& c){
    return c.conclusion.F_terms.size() == conclusion.F_terms.size();
  }), *this);
}

ostream& operator<<(ostream& out, const InductionTemplate& t) {
  outputImplication(out, t.cases, t.conclusion, /*outerParentheses=*/false);
  return out << " [" << ruleName(t.rule) << "]";
}

}
