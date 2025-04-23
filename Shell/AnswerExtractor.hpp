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
 * @file AnswerExtractor.hpp
 * Defines class AnswerExtractor.
 */

#ifndef __AnswerExtractor__
#define __AnswerExtractor__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/TermTransformer.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class AnswerExtractor {
public:
  virtual ~AnswerExtractor() {}

  static void tryOutputAnswer(Clause* refutation);

  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer) = 0;

  void addInputUnit(Unit* unit) { UnitList::push(unit, _inputs); }
protected:
  void getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits);

  UnitList* _inputs = nullptr;
};

class ConjunctionGoalAnswerExractor : public AnswerExtractor {
public:
  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer);

private:
  class SubstBuilder;
};


class AnswerLiteralManager : public AnswerExtractor
{
public:
  static AnswerLiteralManager* getInstance();

  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer);

  void addAnswerLiterals(Problem& prb);
  bool addAnswerLiterals(UnitList*& units);

  virtual void onNewClause(Clause* cl);

  virtual Clause* recordAnswerAndReduce(Clause* cl) { return nullptr; };

protected:
  Clause* getRefutation(Clause* answer);
  Literal* getAnswerLiteral(VList* vars,Formula* f);

private:
  Unit* tryAddingAnswerLiteral(Unit* unit);

  virtual Formula* tryGetQuantifiedFormulaForAnswerLiteral(Unit* unit);

  virtual Unit* createUnitFromConjunctionWithAnswerLiteral(Formula* junction, VList* existsVars, Unit* originalUnit);

  Clause* getResolverClause(unsigned pred);

  RCClauseStack _answers;

  DHMap<unsigned, Clause*> _resolverClauses;
};

typedef std::pair<unsigned, Term*> Binding; 
typedef List<Binding> BindingList;
struct SkolemTracker { // used for tracking skolem terms in the structural induction axiom (recursive program synthesis)
  Binding binding;
  unsigned constructorId; // A skolem constant will be considered computable only in the constructorId'th arg of rec(.)-term
  bool recursiveCall; // Whether the constant corresponds to a recursive call result
  unsigned indexInConstructor; // The index of the variable/Skolem in the constructor OR if 'recursiveCall' is true, to which argument of the constructor the recursive call coresponds to.
  unsigned recFnId; // ID number of the associated rec-function
  SkolemTracker() {}
  SkolemTracker(Binding b, unsigned c, bool rc, unsigned i, unsigned rf = 0) : binding(b), constructorId(c), recursiveCall(rc), indexInConstructor(i), recFnId(rf) {}
  vstring toString() const {
    vstring s;
    s += "SkolemTracker(";
    s += "var=X" + Int::toString(binding.first);
    s += ", skolem=";
    s += (binding.second ? binding.second->toString() : "");
    s += ", cnstrID=";
    s += Int::toString(constructorId);
    s += ", recursiveCall=";
    s += recursiveCall ? "true" : "false";
    s += ", idxInCons=";
    s += Int::toString(indexInConstructor);
    s += ", recFnId=";
    s += Int::toString(recFnId) + ")";
    return s;
  }
};


class SynthesisManager : public AnswerLiteralManager {
 private:
  typedef DHMap<unsigned /*recFnId*/, DHMap<unsigned /*var*/, SkolemTracker>> RecursionMappings;
  class ConjectureSkolemReplacement : public BottomUpTermTransformer {
   public:
    ConjectureSkolemReplacement() {}

    struct Function {
      Function() = default;
      Function(unsigned recFunctor, ConjectureSkolemReplacement* replacement);
      void addCases(Term* t);
      vstring toString() const {
        vstring s;
        vstring fname = env.signature->getFunction(_functor)->name();
        ASS(_cases.size() == _caseHeads->size());
        for (unsigned i = 0; i < _cases.size(); ++i) {
          s += fname + "(" + (*_caseHeads)[i]->toString();
          s += ") = " + _cases[i].toString() + "\n";
        }
        return s;
      }
      unsigned _functor;
      DArray<TermList> _cases;
      std::vector<Term*>* _caseHeads;
      // Mappings of skolems to terms they should be replaced with then construcing the functions for each case.
      DHMap<unsigned, DHMap<Term*, TermList>> _skolemToTermListForCase;
      // A union of replacements for all cases (for convenience).
      DHMap<Term*, TermList> _skolemToTermList;
    };

    void bindSkolemToTermList(Term* t, TermList&& tl);
    TermList transformTermList(TermList tl, TermList sort);
    void addCondPair(unsigned fn, unsigned pred) { _condFnToPred.insert(fn, pred); }
    void associateRecMappings(RecursionMappings* m, DHMap<unsigned, std::vector<Term*>>* f) { _recursionMappings = m; _functionHeads = f;}
    unsigned numInputSkolems() { return _numInputSkolems; }
    void outputRecursiveFunctions();

    DHMap<unsigned, std::vector<Term*>>* _functionHeads;
    const RecursionMappings* _recursionMappings;

   protected:
    TermList transformSubterm(TermList trm) override;

   private:
    unsigned _numInputSkolems = 0;
    // Mapping of input skolems to input variables.
    DHMap<Term*, TermList> _skolemToTermList;
    // Map from functions to predicates they represent in answer literal conditions
    DHMap<unsigned, unsigned> _condFnToPred;
    // Recursive functions indexed by their function symbol number.
    DHMap<unsigned, Function*> _functions; 

    // Term replacement based on a simple mapping with no additional logic.
    class SimpleSkolemReplacement : public TermTransformer {
     public:
      SimpleSkolemReplacement(DHMap<Term*, TermList>* m) : _skolemToTermList(m) {}
      void setMap(DHMap<Term*, TermList>* m) { _skolemToTermList = m; }
     protected:
      TermList transformSubterm(TermList trm) override {
        if (trm.isTerm()) {
          TermList* res = _skolemToTermList->findPtr(trm.term());
          if (res) {
            return *res;
          }
        }
        return trm;
      }
     private:
      DHMap<Term*, TermList>* _skolemToTermList;
    };

  };


  virtual Formula* tryGetQuantifiedFormulaForAnswerLiteral(Unit* unit) override;

  virtual Unit* createUnitFromConjunctionWithAnswerLiteral(Formula* junction, VList* existsVars, Unit* originalUnit) override;

  Formula* getConditionFromClause(Clause* cl);

  Term* translateToSynthesisConditionTerm(Literal* l);

  static Term* createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort);

  static unsigned getITEFunctionSymbol(TermList sort) {
    vstring name = "$ite_" + sort.toString();
    bool added = false;
    unsigned fn = env.signature->addFunction(name, 3, added);
    if (added) {
      Signature::Symbol* sym = env.signature->getFunction(fn);
      sym->setType(OperatorType::getFunctionType({AtomicSort::defaultSort(), sort, sort}, sort));
    }
    return fn;
  }

  ConjectureSkolemReplacement _skolemReplacement;

  List<std::pair<unsigned,std::pair<Clause*, Literal*>>>* _answerPairs = nullptr;

  Literal* _lastAnsLit = nullptr;

  // All SkolemTrackers created during the proof search indexed first by the rec-function symbol number and then by the variable number.
  RecursionMappings _recursionMappings;
  // All SkolemTrackers created during the proof search indexed by the skolem function symbol number.
  DHMap<unsigned, SkolemTracker*> _skolemTrackers;
  // Function heads corresponding to all rec-symbols created in Induction, indexed by the rec-function symbol number.
  DHMap<unsigned, std::vector<Term*>> _functionHeads;

public:
  static SynthesisManager* getInstance();

  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer) override;

  void tryOutputInputUnits();

  virtual void onNewClause(Clause* cl) override;

  virtual Clause* recordAnswerAndReduce(Clause* cl) override;

  Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit);

  // Registers rec-function symbol and initializes a corresponding map in _recursionMappings.
  void registerRecSymbol(unsigned recFnId);
  // Add a new SkolemTracker before skolemization (without the corresponding skolem).
  void addInductionVarData(unsigned recFnId, unsigned var, unsigned consId, bool recCall, unsigned idxInCons);
  // Register the skolem symbol of `recTerm` as rec-symbol, and add information about skolem constants from `binding` into `incompleteTrackers` and store them.
  void registerSkolemSymbols(Term* recTerm, const DHMap<unsigned, Term*>& binding, const List<Term*>* functionHeadsByConstruction, std::vector<SkolemTracker>& incompleteTrackers, const VList* us);

  bool isRecTerm(const Term* t);

  bool hasRecTerm(Literal* lit);

  const SkolemTracker* getSkolemTracker(unsigned skolemFunctor);

  void outputRecursiveFunctions() { _skolemReplacement.outputRecursiveFunctions(); }

  unsigned numInputSkolems() { return _skolemReplacement.numInputSkolems(); }

  void printRecursionMappings();
  void printSkolemTrackers();
};

}

#endif // __AnswerExtractor__
