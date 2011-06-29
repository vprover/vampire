/**
 * @file AnswerExtractor.cpp
 * Implements class AnswerExtractor.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Tabulation/TabulationAlgorithm.hpp"

#include "Shell/Flattening.hpp"
#include "Shell/Options.hpp"

#include "AnswerExtractor.hpp"

#undef LOGGING
#define LOGGING 0


namespace Shell
{

void AnswerExtractor::tryOutputAnswer(Clause* refutation)
{
  CALL("AnswerExtractor::tryOutputAnswer");

  Stack<TermList> answer;

  ConjunctionGoalAnswerExractor ae1;
  if(!ae1.tryGetAnswer(refutation, answer)) {
    return;
  }
  env.beginOutput();
  env.out() << "% SZS answers Tuple [[";
  Stack<TermList>::BottomFirstIterator ait(answer);
  while(ait.hasNext()) {
    TermList aLit = ait.next();
    env.out() << aLit.toString();
    if(ait.hasNext()) {
      env.out() << ',';
    }
  }
  env.out() << "]|_] for " << env.options->problemName() << endl;
  env.endOutput();
}


void AnswerExtractor::getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures)
{
  CALL("AnswerExtractor::getNeededUnits");

  InferenceStore& is = *InferenceStore::instance();

  DHSet<UnitSpec> seen;
  Stack<UnitSpec> toDo;
  toDo.push(UnitSpec(refutation, false));

  while(toDo.isNonEmpty()) {
    UnitSpec curr = toDo.pop();
    if(!seen.insert(curr)) {
      continue;
    }
    Inference::Rule infRule;
    InferenceStore::UnitSpecIterator parents = is.getParents(curr, infRule);
    if(infRule==Inference::NEGATED_CONJECTURE) {
      ASS(curr.withoutProp());
      conjectures.push(curr.unit());
    }
    if(infRule==Inference::CLAUSIFY ||
	(curr.isClause() && (infRule==Inference::INPUT || infRule==Inference::NEGATED_CONJECTURE )) ){
      ASS(curr.withoutProp());
      ASS(curr.isClause());
      premiseClauses.push(static_cast<Clause*>(curr.unit()));
    }
    while(parents.hasNext()) {
      UnitSpec premise = parents.next();
      toDo.push(premise);
    }
  }
}


class ConjunctionGoalAnswerExractor::SubstBuilder
{
public:
  SubstBuilder(LiteralStack& goalLits, LiteralIndexingStructure& lemmas, RobSubstitution& subst)
   : _goalLits(goalLits), _lemmas(lemmas), _subst(subst),
     _goalCnt(goalLits.size()), _btData(_goalCnt), _unifIts(_goalCnt), _triedEqUnif(_goalCnt)
  {}
  ~SubstBuilder()
  {
    CALL("ConjunctionGoalAnswerExractor::SubstBuilder::~SubstBuilder");
    for(unsigned i=0; i<_goalCnt; i++) {
      _btData[i].drop();
    }
  }

  bool run()
  {
    CALL("ConjunctionGoalAnswerExractor::SubstBuilder::run");

    _depth = 0;
    enterGoal();
    for(;;) {
      if(nextGoalUnif()) {
	_depth++;
	if(_depth==_goalCnt) {
	  break;
	}
	enterGoal();
      }
      else {
	leaveGoal();
	if(_depth==0) {
	  return false;
	}
	_depth--;
      }
    }
    ASS_EQ(_depth, _goalCnt);
    //pop the recording data
    for(unsigned i=0; i<_depth; i++) {
      _subst.bdDone();
    }
    return true;
  }

  void enterGoal()
  {
    CALL("ConjunctionGoalAnswerExractor::SubstBuilder::enterGoal");

    _unifIts[_depth] = _lemmas.getUnifications(_goalLits[_depth], false, false);
    _triedEqUnif[_depth] = false;
    _subst.bdRecord(_btData[_depth]);
  }
  void leaveGoal()
  {
    CALL("ConjunctionGoalAnswerExractor::SubstBuilder::leaveGoal");

    _subst.bdDone();
    _btData[_depth].backtrack();
  }
  bool nextGoalUnif()
  {
    CALL("ConjunctionGoalAnswerExractor::SubstBuilder::nextGoalUnif");

    Literal* goalLit = _goalLits[_depth];

    LOGV(goalLit->toString());
    while(_unifIts[_depth].hasNext()) {
      SLQueryResult qres = _unifIts[_depth].next();
      ASS_EQ(goalLit->header(), qres.literal->header());
      LOGV(qres.literal->toString());
      if(_subst.unifyArgs(goalLit, 0, qres.literal, 1)) {
	return true;
      }
    }
    if(!_triedEqUnif[_depth] && goalLit->isEquality() && goalLit->isPositive()) {
      _triedEqUnif[_depth] = true;
      if(_subst.unify(*goalLit->nthArgument(0), 0, *goalLit->nthArgument(1), 0)) {
	return true;
      }
    }
    return false;
  }

private:
  LiteralStack& _goalLits;
  LiteralIndexingStructure& _lemmas;
  RobSubstitution& _subst;

  unsigned _goalCnt;
  DArray<BacktrackData> _btData;
  DArray<SLQueryResultIterator> _unifIts;
  DArray<bool> _triedEqUnif;

  unsigned _depth;
};

bool ConjunctionGoalAnswerExractor::tryGetAnswer(Clause* refutation, Stack<TermList>& answer)
{
  CALL("ConjunctionGoalAnswerExractor::tryGetAnswer");

  ClauseStack premiseClauses;
  Stack<Unit*> conjectures;
  getNeededUnits(refutation, premiseClauses, conjectures);

  if(conjectures.size()!=1 || conjectures[0]->isClause()) {
    return false;
  }
  Formula* form = static_cast<FormulaUnit*>(conjectures[0])->formula();

  form = Flattening::flatten(form);

  if(form->connective()!=NOT) {
    return false;
  }
  form = form->uarg();
  if(form->connective()!=EXISTS) {
    return false;
  }
  Formula::VarList* answerVariables = form->vars();
  form = form->qarg();

  LiteralStack goalLits;
  if(form->connective()==LITERAL) {
    goalLits.push(form->literal());
  }
  else if(form->connective()==AND) {
    FormulaList::Iterator git(form->args());
    while(git.hasNext()) {
      Formula* gf = git.next();
      if(gf->connective()!=LITERAL) {
        return false;
      }
      goalLits.push(gf->literal());
    }
  }
  else {
    return false;
  }

  Tabulation::TabulationAlgorithm talg;
  talg.addInputClauses(pvi( ClauseStack::Iterator(premiseClauses) ));
  MainLoopResult res = talg.run();

  LiteralIndexingStructure& lemmas = talg.getLemmaIndex();

  RobSubstitution subst;

  SLQueryResultIterator alit = lemmas.getAll();
  while(alit.hasNext()) {
    SLQueryResult aqr = alit.next();
    LOGV(aqr.literal->toString());
  }

  if(!SubstBuilder(goalLits, lemmas, subst).run()) {
    return false;
  }

  Formula::VarList::Iterator vit(answerVariables);
  while(vit.hasNext()) {
    int var = vit.next();
    TermList varTerm(var, false);
    TermList asgn = subst.apply(varTerm, 0); //goal variables have index 0
    answer.push(asgn);
  }

  return true;
}


}
