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
 * @file ProofExtra.cpp
 * Various objects that include "extra information" about an inference,
 * e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#include "ProofExtra.hpp"
#include "Kernel/Clause.hpp"

namespace Inferences {

void InferenceReplayInformation::output(std::ostream& out) const {
  out << "conclusion=" << conclusion->number() << ",parents=[";
  for (unsigned bank = 0; bank < premises.size(); ++bank) {
    if (bank) { out << ','; }
    out << premises[bank]->number() << ':' << substitutionForBanksSub[bank];
  }
  out << ']';
}

void SynthesisInferenceExtra::output(std::ostream& out) const {
  if (condition) {
    out << "condition=(" << condition->toString() << ')';
  }
  if (thenLit) {
    if (condition) { out << ','; }
    out << "thenLit=(" << thenLit->toString() << ',' << thenLit << ')';
  }
  if (elseLit) {
    if (condition || thenLit) { out << ','; }
    out << "elseLit=(" << elseLit->toString() << ',' << elseLit << ')';
  }
}

void ConstraintInformation::output(std::ostream& out) const {
  out << "constraints=[";
  for (unsigned i = 0; i < literals.size(); ++i) {
    if (i) { out << ','; }
    out << *literals[i];
  }
  out << ']';
}

} // namespace Inferences
