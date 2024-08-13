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

#include <map>

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/RCClauseStack.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Inferences/InferenceEngine.hpp"

namespace Inferences {

/*
* If the given clause only contains answer literals, resolved them all away
* (formally via URR) by using the into-the-search-space-not-inserted ANSWER_LITERAL_RESOLVERs.
* the resulting clause is empty (modulo splits, which we tolarate).
*/
class AnswerLiteralResolver
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

}

namespace Shell {

using namespace Kernel;
using namespace Indexing;

class AnswerLiteralManager
{
public:
  friend class Inferences::AnswerLiteralResolver;
  /**
   * There should be at most one AnswerLiteralManager instance in the whole wide world.
   * Depending on Lib::env.options this will be
   * - either AnswerLiteralManager proper (for QuestionAnsweringMode::PLAIN)
   * - or a SynthesisALManager (for QuestionAnsweringMode::SYNTHESIS)
   */
  static AnswerLiteralManager* getInstance();

  void tryOutputAnswer(Clause* refutation, std::ostream& out);

  virtual ~AnswerLiteralManager() {}

  virtual bool tryGetAnswer(Clause* refutation, Lib::Stack<Clause*>& answer);

  void addAnswerLiterals(Problem& prb);
  bool addAnswerLiterals(UnitList*& units);

  virtual void onNewClause(Clause* cl) {}

  // The following function currently only make sense in SYNTHESIS:
  virtual Clause* recordAnswerAndReduce(Clause* cl) { return nullptr; };
  virtual Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) { return nullptr; };

  /**
  * Record an assiciation between a skolem symbol and the pair <the variable it replaces, in which formula>
  */
  void recordSkolemsOrigin(unsigned skSymb, unsigned var, Unit* unit) {
    ALWAYS(_skolemsOrigin.insert(skSymb,std::make_pair(var,unit)));
  }

protected:
  static TermList possiblyEvaluateAnswerTerm(TermList);

  /**
   * Tell the concrete implemenation (our descentants) that we have just introduced
   * a new skolem symbol term skT to replace var in the conjecture/question;
   * Ideally ("the user might expect"), the var should be referred to as vName in the answers.
   */
  virtual void recordSkolemBinding(Term* skT,unsigned var,std::string vName) = 0;
  virtual bool closeFreeVariablesForPrinting() { return false; };
  virtual void optionalAnswerPrefix(std::ostream& out) {};
  virtual std::string postprocessAnswerString(std::string answer) { return answer; };

  Clause* getRefutation(Clause* answer);
  Literal* getAnswerLiteral(VList* vars,SList* srts,Formula* f);

private:
  Unit* tryAddingAnswerLiteral(Unit* unit);

  Clause* getResolverClause(unsigned pred);

  /**
   * So that for every answer-predicate-symbol (key)
   * we can retrieve the unit for which it was introduced
   * and the Literal that got injected into the conjecture
   * (which, in particular, has the variables for arguments
   * as they were in the conecture).
   */
  Lib::DHMap<unsigned, std::pair<Unit*,Literal*>> _originUnitsAndInjectedLiterals;

  Lib::DHMap<unsigned, Clause*> _resolverClauses;

  Lib::DHMap<unsigned,std::pair<unsigned,Unit*>> _skolemsOrigin;
};

class PlainALManager : public AnswerLiteralManager
{
protected:
  void recordSkolemBinding(Term*,unsigned,std::string) override;
  bool closeFreeVariablesForPrinting() override { return true; };
  void optionalAnswerPrefix(std::ostream& out) override;
  std::string postprocessAnswerString(std::string answer) override;
private:
  Lib::Stack<std::pair<Term*, std::string>> _skolemNames;
};

class SynthesisALManager : public AnswerLiteralManager
{
public:
  bool tryGetAnswer(Clause* refutation, Lib::Stack<Clause*>& answer) override;
  void onNewClause(Clause* cl) override;

  Clause* recordAnswerAndReduce(Clause* cl) override;

  Literal* makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) override;

protected:
  void recordSkolemBinding(Term*,unsigned,std::string) override;

private:
  void getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Lib::Stack<Unit*>& conjectures, Lib::DHSet<Unit*>& allProofUnits);

  class ConjectureSkolemReplacement : public TermTransformer {
   public:
    ConjectureSkolemReplacement() : _skolemToVar() {}
    void bindSkolemToVar(Term* t, unsigned v);
    TermList transformTermList(TermList tl, TermList sort);
    void addCondPair(unsigned fn, unsigned pred) { _condFnToPred.insert(fn, pred); }
   protected:
    TermList transformSubterm(TermList trm) override;
   private:
    std::map<Term*, unsigned> _skolemToVar;
    // Map from functions to predicates they represent in answer literal conditions
    Lib::DHMap<unsigned, unsigned> _condFnToPred;
  };

  Formula* getConditionFromClause(Clause* cl);

  Term* translateToSynthesisConditionTerm(Literal* l);

  static Term* createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort);

  static unsigned getITEFunctionSymbol(TermList sort) {
    std::string name = "$ite_" + sort.toString();
    bool added = false;
    unsigned fn = Lib::env.signature->addFunction(name, 3, added);
    if (added) {
      Signature::Symbol* sym = Lib::env.signature->getFunction(fn);
      sym->setType(OperatorType::getFunctionType({AtomicSort::defaultSort(), sort, sort}, sort));
    }
    return fn;
  }

  ConjectureSkolemReplacement _skolemReplacement;

  Lib::List<std::pair<unsigned,std::pair<Clause*, Literal*>>>* _answerPairs = nullptr;

  Literal* _lastAnsLit = nullptr;
};

}

#endif // __AnswerLiteralManager__
