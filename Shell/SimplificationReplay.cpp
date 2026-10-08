/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#include "SimplificationReplay.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

namespace Shell::SimplificationReplay {
using namespace Kernel;

// Forward literal rewriting orients a rewrite rule at search time between two
// complementary-variant two-literal clauses, but records only one of them as
// the premise: the counterpart merely orients the rule, the conclusion already
// follows from the recorded premise by binary resolution. Replay that
// resolution directly on the two recorded parents. Search-time retrieval is
// one-way -- the premise's rule-side literal is a generalization of the
// rewritten literal -- so the matcher never binds the main clause's variables
// and the main clause's other literals are retained unchanged.
void literalRewriting(Clause* main, Clause* premise)
{
  if (premise->length() != 2) {
    return;
  }
  for (unsigned i = 0; i < main->length(); ++i) {
    Literal* lit = (*main)[i];
    for (unsigned j = 0; j < 2; ++j) {
      // The rule side has the opposite polarity of the literal it rewrites.
      Literal* ruleSide = (*premise)[j];
      if (ruleSide->isNegative() == lit->isNegative() ||
          !ruleSide->containsAllVariablesOf((*premise)[1 - j])) {
        continue;
      }
      Substitution matcher;
      if (!MatchingUtils::match(ruleSide, lit, /*complementary=*/true, matcher)) {
        continue;
      }
      RStack<Literal*> resLits;
      resLits->push(SubstHelper::apply((*premise)[1 - j], matcher));
      for (unsigned k = 0; k < main->length(); ++k) {
        if (k != i) {
          resLits->push((*main)[k]);
        }
      }
      Clause* conclusion = Clause::fromStack(*resLits,
          SimplifyingInference2(InferenceRule::FORWARD_LITERAL_REWRITING, main, premise));
      std::vector<Substitution> substitutions(2);
      auto variables = premise->getVariableIterator();
      while (variables.hasNext()) {
        unsigned variable = variables.next();
        substitutions[1].bind(variable, matcher.apply(variable));
      }
      if (InferenceRecorder::instance()->recordReplayedInferenceCandidate(conclusion, {main, premise},
          substitutions,
          InferenceRecorder::InferenceInformation::LiteralPositionKind::RESOLVED,
          {{0, i}, {1, j}})) {
        return;
      }
      conclusion->destroy();
    }
  }
}

// Search accepts its first successful simplification. Replay must reproduce
// the recorded removed occurrence, which may be a later solver alternative.
void subsumptionResolution(Clause* main, Clause* side)
{
  SATSubsumption::SATSubsumptionAndResolution checker;
  for (unsigned i = 0; i < main->length(); ++i) {
    if (!checker.checkSubsumptionResolutionWithLiteral(side, main, i)) { continue; }
    auto substitution = checker.getBindingsForSubsumptionResolutionWithLiteral();
    Clause* candidate = checker.getSubsumptionResolutionConclusion(main, (*main)[i], side, /*forward=*/false);
    if (InferenceRecorder::instance()->recordReplayedInferenceCandidate(candidate, {main, side},
          std::vector<Substitution>{Substitution(), substitution},
          InferenceRecorder::InferenceInformation::LiteralPositionKind::REMOVED, {{0, i}})) { return; }
    candidate->destroy();
  }
}

} // namespace Shell::SimplificationReplay
