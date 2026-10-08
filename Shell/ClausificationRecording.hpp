/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#ifndef __Shell_ClausificationRecording__
#define __Shell_ClausificationRecording__

#include "Forwards.hpp"
#include "Lib/ProofExtra.hpp"

#include <utility>
#include <vector>

namespace Shell {

/** Captured before selection changes literal order. Occurrences follow the
 * printed parent, including duplicates and printed equality orientations. */
struct ClausificationExtra : Lib::InferenceExtra {
  struct Occurrence {
    Kernel::Literal* instantiated;
    bool flipped;
  };
  std::vector<std::pair<unsigned, unsigned>> binders;
  std::vector<Occurrence> occurrences;
  void output(std::ostream& out) const override { out << "clausification_certificate"; }
};

/** Capture only a universal prefix followed by a clause-shaped body. Old CNF
 * preserves literal identities and variable names, so no matching or replay
 * is needed. Unsupported formulas and vacuous binders get no certificate. */
void recordClausification(Kernel::FormulaUnit* parent, Kernel::Clause* conclusion);

} // namespace Shell
#endif
