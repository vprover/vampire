
#include "Forwards.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Unit.hpp"
#include "LeanPrinter.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include "Saturation/Splitter.hpp"
#include <initializer_list>
#include <ostream>
#include <deque>
#include <queue>
#include <string>
#include <map>
namespace Shell {
using namespace LeanPrinter;
class LeanChecker : public InferenceStore::AbstractProofPrinter {
public:
  LeanChecker(std::ostream &out, InferenceStore *is) : AbstractProofPrinter(out, is), _replayer(out) {
    _replayer.makeInferenceEngine(this->_is->ordering);
  }

  void print() override;

  void printStep(Unit *u) override {} // do nothing as we need to call other methods anyway

  void outputPreamble(std::ostream &out);

  void outputInferenceStep(std::ostream &out, Kernel::Unit *u);

  void outputProofStep(std::ostream &out, Kernel::Unit *u);

private:

  bool isUncheckedInference(const InferenceRule &rule);

  bool isUncheckedInProof(const InferenceRule &rule);

  bool doesOutputSplits(const InferenceRule &rule);

  bool inferenceNeedsReplayInformation(const InferenceRule &rule);

  void outputCumulativeSplits(std::initializer_list<Kernel::Clause *> cl, std::string seperator = " ",std::string splitPrefix = "sA", bool ignoreNegation = false);

  void outputCumulativeSplits(std::set<Kernel::Unit*, CompareUnits> cl, std::string seperator = " ", std::string splitPrefix = "sA", std::string prefix = "", std::string suffix = "");

  void outputUnit(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts = nullptr, bool outputSplits = true);

  void outputUnitBeginning(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts = nullptr);

  template <typename Transform = Identity>
  void outputClause(std::ostream &out, Kernel::Clause* cl, SortMap *conclSorts = nullptr, Transform transform = Transform{}){
    if(cl->isEmpty()){
      out << "False";
      return;
    }
    out << "(";
    bool first = true;
    SortMap sorts;
    SortHelper::collectVariableSorts(cl, sorts);
    outputSortsWithQuantor(out, sorts);
    for (Literal *l : *cl) {
      if (!first){
        if(LeanPrinter::outputBoolOperators){
          out << " || ";
        } else {
          out << " ∨ ";
        }
      }
      l = transform(l);
      if (conclSorts!=nullptr)
        out << Lit{l, *conclSorts, sorts};
      else
        out << Lit{l, sorts, sorts};
      first = false;
    }
    out << ")";
  }

  template <typename Transform = Identity>
  void outputFormula(std::ostream &out, Kernel::Formula* f, SortMap *conclSorts = nullptr,Transform transform = Transform{}){
    //out << "(";
    SortMap sorts;
    SortHelper::collectVariableSorts(f, sorts);
    if (conclSorts!=nullptr)
      printFormula(out, f, *conclSorts, sorts);
    else
      printFormula(out, f, sorts, sorts);
    //out << ")";
  }

  unsigned outputPremises(std::ostream &out, Unit *u, std::string seperator = " →\n");
  void outputPremiseAndConclusion(std::ostream &out, Unit *concl, std::string separator = " →\n");
  void instantiateConclusionVars(std::ostream &out, SortMap &conclSorts, Unit *concl);
  template <typename Transform = Identity>
  void instantiatePremiseVars(std::ostream &out, SortMap &conclSorts, Unit *premise, Transform transform = Transform{}){
    if(premise->isClause()){
      auto cl = premise->asClause();
      if(!cl->noSplits()){
        if(cl->splits()->size() > 1){
          out << "and_constr ⟨";
        }
        outputCumulativeSplits({cl}, ", ", "x", true);
        if(cl->splits()->size() > 1){
          out << "⟩";
        } 
        out << " ";
      }
    }
    SortMap premiseSorts;
    SortHelper::collectVariableSorts(premise, premiseSorts);
    VirtualIterator<unsigned> domain = premiseSorts.domain();
    outputVariablesGen(out, domain, conclSorts, premiseSorts, transform);
  }

  void genericNPremiseInference(std::ostream &out, SortMap &conclSorts, Clause *concl, std::initializer_list<Substitution> substitutions, std::string tactic = "grind only");
  void genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Clause *concl, std::string tactic = "grind only");
  void genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic = "grind only");

  void genericInference(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic = "duper [*]");
  void subsumptionResolution(std::ostream &out, SortMap &conclSorts, Clause *concl);
  void            resolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void             factoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void    equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void         superposition(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void          demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void              clausify(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void predicateDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void  functionDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void    avatarDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void       avatarComponent(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void outputSatClause(std::ostream &out, std::map<unsigned int, bool> &seen, std::string primed = "'", bool boolSymbols = false);
  void outputSatFormula(std::ostream &out, std::set<Unit *, CompareUnits> &parents, std::string primed = "'", bool useBoolOperators = false, bool useImplication = false);
  void avatarRefutation(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void avatarRefutationProofStep(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void avatarSplitClause(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void            normalForm(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void             skolemize(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void definitionFoldingTwee(std::ostream &out, SortMap &conclSorts, Clause *concl);
  void definitionFoldingPred(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void definitionUnfolding(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void                 axiom(std::ostream &out, SortMap &conclSorts, Unit *concl);

  void outputFullProofPreamble(std::ostream &out, std::deque<Unit*> premises, std::deque<Unit*> negatedConjectures);


  private:
  std::queue<std::pair<unsigned,unsigned>> skolemSymbols; // pair is (symbol number, replaced var)

  std::set<unsigned> alreadyPrintedFormulas;
  InferenceReplayer _replayer;

  std::string preambleLean = "-- Lean proof output generated by Vampire\n"
         //"import Mathlib.Order.Basic\n"
         //"import Mathlib.Data.Real.Basic\n"
         "import Lean\n"
         "import Duper\n"
         "import Mathlib.Tactic.NthRewrite\n"
         "import VampLean.Helpers\n"
         "universe u\n"
         "set_option linter.style.longLine false\n"
         "set_option linter.unusedSectionVars false\n"
         "set_option linter.unusedTactic false\n"
         "set_option linter.unusedSimpArgs false\n"
         "set_option linter.unusedVariables false\n"
         "set_option linter.unnecessarySeqFocus false\n"
         "set_option linter.unreachableTactic false\n\n"
         //"set_option linter.unreachableTactic false\n\n"
         "set_option maxRecDepth 100000\n\n";
         //"def inhabit_ℤ : ℤ := default\n"
         //"def inhabit_ℝ : ℝ := default\n"
         //"def inhabit_Bool : Bool := default\n";
 
  const std::string stepIdent = "step";
  const std::string indent = "  ";
  const std::string intIdent = "i";
  const std::string avatarSplitPrefix = "sA";
 
};
} // namespace Shell