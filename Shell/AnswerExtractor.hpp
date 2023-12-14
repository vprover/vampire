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

  void tryOutputInputUnits();

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
    unsigned constructorIndex; // a skolem constant will be considered computable in the j'th arg of rec(.), if j = constructorIndex
    bool recursiveArg; // E.g., BT(l, n, r) is recursive in arg 0 and 2, but not in arg 1
    int recursivePos; // -1 if not recursive, otherwise the position of the recursive argument
    int recFnID; // the ID of the rec(.) function in the structural induction axiom
    SkolemTracker(Binding b, unsigned c, bool r, int pos, int rec_fn) : binding(b), constructorIndex(c), recursiveArg(r), recursivePos(pos), recFnID(rec_fn) {}
    vstring toString() {
      vstring s;
      s += "SkolemTracker(";
      s += "var=X" + Int::toString(binding.first);
      s += ", skolem=";
      s += binding.second->toString();
      s += ", cnstrID=";
      s += Int::toString(constructorIndex);
      s += ", recursiveArg=";
      s += recursiveArg ? "true" : "false";
      s += ", recPos=";
      s += Int::toString(recursivePos);
      s += ", recFnID=";
      s += Int::toString(recFnID) + ")";
      return s;
    }
  };
  typedef List<SkolemTracker> SkolemTrackerList;



class SynthesisManager : public AnswerLiteralManager
{

private:
  class ConjectureSkolemReplacement : public TermTransformer {
   public:
    ConjectureSkolemReplacement() : _skolemToVar() {}
    void bindSkolemToVar(Term* t, unsigned v);
    TermList transformTermList(TermList tl, TermList sort);
    void addCondPair(unsigned fn, unsigned pred) { _condFnToPred.insert(fn, pred); }
   protected:
    TermList transformSubterm(TermList trm) override;
   private:
    vmap<Term*, unsigned> _skolemToVar;
    // Map from functions to predicates they represent in answer literal conditions
    DHMap<unsigned, unsigned> _condFnToPred;
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

  SkolemTrackerList* _skolemMappings = SkolemTrackerList::empty();      // Stores the final SkolemTracker mappings after skolemization 
  List<unsigned int>* _recTermIds;                                      // Stores the IDs of the rec(.) terms in the structural induction axiom

public:
  static SynthesisManager* getInstance();

  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer) override;

  virtual void onNewClause(Clause* cl) override;

  virtual Clause* recordAnswerAndReduce(Clause* cl) override;

  Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit);

  void storeSkolemMapping(unsigned int var, Term* skolem, unsigned int constructorIndex, bool recursiveArg, int recursivePos, int recFnID);
  void matchSkolemSymbols(BindingList* bindingList, SkolemTrackerList* tempSkolemMappings); // called after skolemization has happened to fill _skolemMappings
  void storeRecTerm(unsigned int fnId) { _recTermIds->push(fnId, _recTermIds); }
  bool isRecTerm(Term* t);
  SkolemTrackerList* getSkolemMappings() { return _skolemMappings; }
  bool hasRecTerm(Literal* lit);
  unsigned int getResolventLiteralIdx(Clause* clause);

  void printSkolemMappings();
};

}

#endif // __AnswerExtractor__
