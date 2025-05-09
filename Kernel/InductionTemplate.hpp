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
 * @file InductionTemplate.hpp
 * Defines class InductionTemplate.
 */

#ifndef __InductionTemplate__
#define __InductionTemplate__
 
#include "Lib/Metaiterators.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"

#include "Kernel/Inference.hpp"

using namespace std;

namespace Kernel {

struct InductionUnit {
  InductionUnit(TermStack&& F_terms, LiteralStack&& conditions = LiteralStack())
    : F_terms(F_terms), conditions(conditions)
  {
    ASS(F_terms.isNonEmpty());
  }

  friend ostream& operator<<(ostream& out, const InductionUnit& u) {
    for (const auto& c : u.conditions) {
      out << *c << " & ";
    }
    out << "=> F[";
    for (const auto& t : u.F_terms) {
      out << t << ",";
    }
    return out << "]";
  }

  TermStack F_terms;
  LiteralStack conditions;
};

struct InductionCase {
  InductionCase(InductionUnit&& conclusion, Stack<InductionUnit>&& hypotheses = Stack<InductionUnit>())
    : conclusion(conclusion), hypotheses(hypotheses)
  {
    ASS(iterTraits(hypotheses.iter()).all([&](const auto& h){
      return h.F_terms.size() == conclusion.F_terms.size();
    }));
  }

  friend ostream& operator<<(ostream& out, const InductionCase& c) {
    for (const auto& h : c.hypotheses) {
      out << "(" << h << ") & ";
    }
    return out << " => (" << c.conclusion << ")";
  }

  InductionUnit conclusion;
  Stack<InductionUnit> hypotheses;
};

/**
 * Similar to a second-order formula that we use for induction,
 * with one universally-quantified second-order variable.
 */
struct InductionTemplate
{
  InductionTemplate(Stack<InductionCase>&& cases, InductionUnit&& conclusion, InferenceRule rule)
    : cases(cases), conclusion(conclusion), rule(rule)
  {
    ASS_REP(iterTraits(cases.iter()).all([&](const auto& c){
      return c.conclusion.F_terms.size() == conclusion.F_terms.size();
    }), *this);
  }

  friend ostream& operator<<(ostream& out, const InductionTemplate& t) {
    for (const auto& c : t.cases) {
      out << "(" << c << ") & ";
    }
    return out << " => (" << t.conclusion << ") " << ruleName(t.rule);
  }

  Stack<InductionCase> cases;
  InductionUnit conclusion;
  InferenceRule rule;
};

}

#endif // __InductionTemplate__
