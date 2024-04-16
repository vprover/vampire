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
 * @file AnswerLiteralManager.hpp
 * Defines class AnswerLiteralManager.
 */

#ifndef __AnswerLiteralManager__
#define __AnswerLiteralManager__

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

class AnswerLiteralManager
{
public:
  virtual ~AnswerLiteralManager() {}
  static void tryOutputAnswer(Clause* refutation);
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

class SynthesisManager : public AnswerLiteralManager
{
public:
  static SynthesisManager* getInstance();

  bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer) override;
  void onNewClause(Clause* cl) override;

  Clause* recordAnswerAndReduce(Clause* cl) override;

  Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit);

private:
  void getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits);

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
};

}

#endif // __AnswerLiteralManager__
