/**
 * @file AnswerExtractor.hpp
 * Defines class AnswerExtractor.
 */

#ifndef __AnswerExtractor__
#define __AnswerExtractor__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/RCClauseStack.hpp"



namespace Shell {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class AnswerExtractor {
public:
  virtual ~AnswerExtractor() {}

  static void tryOutputAnswer(Clause* refutation);

  virtual bool tryGetAnswer(Clause* refutation, Stack<TermList>& answer) = 0;
protected:
  typedef InferenceStore::UnitSpec UnitSpec;
  void getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures);
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

  void addAnswerLiterals(UnitList*& units);

  bool isAnswerLiteral(Literal* lit);

  void onNewClause(Clause* cl);

private:
  Literal* getAnswerLiteral(Formula::VarList* vars);
  Unit* tryAddingAnswerLiteral(Unit* unit);

  Clause* getResolverClause(unsigned pred);
  Clause* getRefutation(Clause* answer);

  RCClauseStack _answers;

  DHMap<unsigned, Clause*> _resolverClauses;
};

}

#endif // __AnswerExtractor__
