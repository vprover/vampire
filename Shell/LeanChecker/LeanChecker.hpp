
#include "Forwards.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/Unit.hpp"
#include "LeanPrinter.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"
#include <map>
#include <ostream>
#include <deque>
#include <queue>
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

  bool inferenceNeedsReplayInfromation(const InferenceRule &rule);

  void outputUnit(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts = nullptr){
    if(this->alreadyPrintedFormulas.find(u->number()) != this->alreadyPrintedFormulas.end()){
      out << "φ" << u->number();
      return;
    }
    if(u->isClause()){
      outputClause(out, u->asClause(), conclSorts, Identity{});
    } else {
      outputFormula(out, u->getFormula(), conclSorts, Identity{});
    }
  }
  
  void outputUnitBeginning(std::ostream &out, Kernel::Unit *u, SortMap *conclSorts = nullptr){
    auto parents = u->getParents();
    while(parents.hasNext()){
      auto parent = parents.next();
      if(this->alreadyPrintedFormulas.find(parent->number()) == this->alreadyPrintedFormulas.end()){
         out << "def φ" << parent->number() << " :=";
         outputUnit(out, parent);
         out << "\n";
      }
      alreadyPrintedFormulas.insert(parent->number());
    }
    //if(this->alreadyPrintedFormulas.find(u->number()) == this->alreadyPrintedFormulas.end()){
    //  out << "def φ" << u->number() << " :=";
    //  outputUnit(out, u);
    //  out << "\n";
    //  alreadyPrintedFormulas.insert(u->number());
    //}
  }

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
      if (!first)
        out << " ∨ ";
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

  unsigned outputPremises(std::ostream &out, Unit *u);
  void outputPremiseAndConclusion(std::ostream &out, Unit *concl);
  void instantiateConclusionVars(std::ostream &out, SortMap &conclSorts, Unit *concl);
  template <typename Transform = Identity>
  void instantiatePremiseVars(std::ostream &out, SortMap &conclSorts, Unit *premise, Transform transform = Transform{}){
    SortMap premiseSorts;
    SortHelper::collectVariableSorts(premise, premiseSorts);
    VirtualIterator<unsigned> domain = premiseSorts.domain();
    outputVariablesGen(out, domain, conclSorts, premiseSorts, transform);
  }

  void genericNPremiseInference(std::ostream &out, SortMap &conclSorts, Clause *concl, std::initializer_list<Substitution> substitutions, std::string tactic = "grind only");
  void genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Clause *concl, std::string tactic = "grind only");
  void genericNPremiseInferenceNoSubs(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic = "grind only");

  void genericInference(std::ostream &out, SortMap &conclSorts, Unit *concl, std::string tactic = "grind");
  void subsumptionResolution(std::ostream &out, SortMap &conclSorts, Clause *concl);
  void            resolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void             factoring(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void    equalityResolution(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void         superposition(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void          demodulation(std::ostream &out, SortMap &conclSorts, Clause *concl, const InferenceRecorder::InferenceInformation* info);
  void              clausify(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void predicateDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void  functionDefinitionIntroduction(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void            normalForm(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void             skolemize(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void definitionFoldingTwee(std::ostream &out, SortMap &conclSorts, Clause *concl);
  void definitionFoldingPred(std::ostream &out, SortMap &conclSorts, Unit *concl);
  void                 axiom(std::ostream &out, SortMap &conclSorts, Unit *concl);

  void outputFullProofPreamble(std::ostream &out, std::deque<Unit*> premises, std::deque<Unit*> negatedConjectures);


  private:
  std::queue<std::pair<unsigned,unsigned>> skolemSymbols; // pair is (symbol number, replaced var)

  std::set<unsigned> alreadyPrintedFormulas;
  InferenceReplayer _replayer;

  std::string preambleLean = "-- Lean proof output generated by Vampire\n"
         "import Mathlib.Order.Basic\n"
         "import Mathlib.Data.Real.Basic\n"
         "import Lean\n"
         "import LeanTest.Superposition\n"
         "import LeanTest.quantifierChange\n"
         "open Lean Elab Tactic Meta\n"
         "universe u\n"
         "set_option linter.style.longLine false\n"
         "set_option linter.unusedSectionVars false\n"
         "set_option linter.unusedTactic false\n"
         "set_option linter.unusedSimpArgs false\n\n"

         "def inhabit_ℤ : ℤ := default\n"
         "def inhabit_ℝ : ℝ := default\n"
         "def inhabit_Bool : Bool := default\n";

  std::string stepIdent = "step";
  std::string indent = "  ";
  std::string intIdent = "i";  

};
} // namespace Shell