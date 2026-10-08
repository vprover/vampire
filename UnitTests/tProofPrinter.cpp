/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Problem.hpp"
#include "SAT/SATInference.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/Options.hpp"

#include <sstream>

using namespace Kernel;
using namespace Test;

TEST_FUN(abstract_printer_traverses_hidden_shared_parents_and_additional_dependencies)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto seed = clause({p(a)});
  auto definition = clause({p(a)});
  auto hidden = clause({p(a)},
      SimplifyingInference1(InferenceRule::REMOVE_DUPLICATE_LITERALS, seed));
  auto goal = clause({p(a)}, GeneratingInference2(InferenceRule::RESOLUTION, hidden, hidden));

  struct Printer : InferenceStore::AbstractProofPrinter {
    Printer(std::ostream& out, Unit* goal, Unit* definition)
      : AbstractProofPrinter(out, InferenceStore::instance()), goal(goal), definition(definition) {}
    Unit* goal;
    Unit* definition;
    unsigned visited = 0;

    bool hideProofStep(InferenceRule rule) override {
      return rule == InferenceRule::REMOVE_DUPLICATE_LITERALS;
    }
    void addAdditionalPremises(Unit* unit, std::vector<Unit*>& todo) override {
      ++visited;
      if (unit == goal) { todo.push_back(definition); }
    }
    void printStep(Unit* unit) override { out << unit->number() << '\n'; }
  };

  std::ostringstream out;
  Printer printer(out, goal, definition);
  printer.scheduleForPrinting(goal);
  printer.scheduleForPrinting(goal);
  printer.scheduleForPrinting(definition);
  printer.print();
  ASS_EQ(printer.visited, 4);
  ASS_EQ(out.str(), std::to_string(seed->number()) + '\n' +
      std::to_string(definition->number()) + '\n' + std::to_string(goal->number()) + '\n');
}

TEST_FUN(proof_formats_emit_sat_steps_only_in_human_and_tptp_output)
{
  auto sort = AtomicSort::defaultSort();
  DECL_CONST(a, sort)
  DECL_PRED(p, {sort})
  auto seed = clause({p(a)});
  auto conversion = new(1) SAT::SATClause(1);
  (*conversion)[0] = SAT::SATLiteral(1, true);
  conversion->setInference(new SAT::FOConversionInference(seed));
  env.proofExtra.insert(seed, new Saturation::SATClauseExtra(conversion));
  auto refutation = new(0) SAT::SATClause(0);
  refutation->setInference(new SAT::PropInference(conversion));
  auto goal = clause(Stack<Lit>(), InferenceOfASatClause(InferenceRule::AVATAR_REFUTATION,
      refutation, UnitList::singleton(seed)));

  Problem problem;
  problem.addUnits(UnitList::singleton(goal));
  env.setMainProblem(&problem);
  env.options->resolveAwayAutoValues0();
  env.options->resolveAwayAutoValues(problem);
  env.options->set("proof_extra", "full");
  auto store = InferenceStore::instance();
  store->ordering = OrderingSP(Ordering::create(problem, *env.options));
  std::ostringstream satText;
  satText << *refutation;
  auto tptpPrefix = "cnf(s" + std::to_string(refutation->number) + ',';

  for (auto mode : {"on", "tptp", "property", "proofcheck", "smt2_proofcheck", "smtcheck"}) {
    env.options->set("proof", mode);
    std::ostringstream out;
    store->outputProof(out, goal);
    auto text = out.str();
    ASS_EQ(text.find(satText.str()) != std::string::npos, std::string(mode) == "on");
    ASS_EQ(text.find(tptpPrefix) != std::string::npos, std::string(mode) == "tptp");
    if (std::string(mode) == "tptp") {
      auto conversionPosition = text.find("cnf(s" + std::to_string(conversion->number) + ',');
      ASS(conversionPosition < text.find(tptpPrefix));
      ASS(text.find(tptpPrefix) < text.find("fof(f" + std::to_string(goal->number()) + ','));
    }
  }
}
