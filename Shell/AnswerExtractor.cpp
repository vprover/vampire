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
 * @file AnswerExtractor.cpp
 * Implements class AnswerExtractor.
 */

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/System.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"

// #include "Tabulation/TabulationAlgorithm.hpp" // MS: Tabulation discontinued, AnswerExtractor needs fixing
#include "Indexing/Index.hpp"
#include "Indexing/LiteralIndexingStructure.hpp"

#include "Shell/Flattening.hpp"
#include "Shell/Options.hpp"

#include "AnswerExtractor.hpp"


namespace Shell
{

void AnswerExtractor::tryOutputAnswer(Clause* refutation)
{
  CALL("AnswerExtractor::tryOutputAnswer");

  Stack<TermList> answer;

  if(!AnswerLiteralManager::getInstance()->tryGetAnswer(refutation, answer)) {
    ConjunctionGoalAnswerExractor cge;
    if(!cge.tryGetAnswer(refutation, answer)) {
      return;
    }
  }
  env.beginOutput();
  env.out() << "% SZS answers Tuple [[";
  Stack<TermList>::BottomFirstIterator ait(answer);
  while(ait.hasNext()) {
    TermList aLit = ait.next();
    // try evaluating aLit
    if(aLit.isTerm()){
      InterpretedLiteralEvaluator eval;
      unsigned p = env.signature->addFreshPredicate(1,"p"); 
      TermList sort = SortHelper::getResultSort(aLit.term());
      OperatorType* type = OperatorType::getPredicateType({sort});
      env.signature->getPredicate(p)->setType(type);
      Literal* l = Literal::create1(p,true,aLit); 
      Literal* res =0;
      bool constant, constTrue;
      Stack<Literal*> sideConditions;
      bool litMod = eval.evaluate(l,constant,res,constTrue,sideConditions);
      if(litMod && res && sideConditions.isEmpty()){
        aLit.setTerm(res->nthArgument(0)->term());
      }
    }

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

  DHSet<Unit*> seen;
  Stack<Unit*> toDo;
  toDo.push(refutation);

  while(toDo.isNonEmpty()) {
    Unit* curr = toDo.pop();
    if(!seen.insert(curr)) {
      continue;
    }
    InferenceRule infRule;
    UnitIterator parents = is.getParents(curr, infRule);
    if(infRule==InferenceRule::NEGATED_CONJECTURE) {
      conjectures.push(curr);
    }
    if(infRule==InferenceRule::CLAUSIFY ||
	(curr->isClause() && (infRule==InferenceRule::INPUT || infRule==InferenceRule::NEGATED_CONJECTURE )) ){
      ASS(curr->isClause());
      premiseClauses.push(curr->asClause());
    }
    while(parents.hasNext()) {
      Unit* premise = parents.next();
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

    while(_unifIts[_depth].hasNext()) {
      SLQueryResult qres = _unifIts[_depth].next();
      ASS_EQ(goalLit->header(), qres.literal->header());
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
  VList* answerVariables = form->vars();
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

  Options tabulationOpts;
  //tabulationOpts.setSaturationAlgorithm(Options::SaturationAlgorithm::TABULATION);
  //NOT_IMPLEMENTED;

  // MS: Tabulation discontinued, AnswerExtractor needs fixing
  (void)answerVariables;
  /*
  Problem tabPrb(pvi( ClauseStack::Iterator(premiseClauses) ), true);
  Tabulation::TabulationAlgorithm talg(tabPrb, tabulationOpts);
  talg.run();

  LiteralIndexingStructure& lemmas = talg.getLemmaIndex();

  RobSubstitution subst;

  SLQueryResultIterator alit = lemmas.getAll();
  while(alit.hasNext()) {
    SLQueryResult aqr = alit.next();
  }

  if(!SubstBuilder(goalLits, lemmas, subst).run()) {
    cout << "Answer not found in proof" << endl;
    return false;
  }

  Formula::VarList::Iterator vit(answerVariables);
  while(vit.hasNext()) {
    int var = vit.next();
    TermList varTerm(var, false);
    TermList asgn = subst.apply(varTerm, 0); //goal variables have index 0
    answer.push(asgn);
  }

  */

  return true;
}


///////////////////////
// AnswerLiteralManager
//

AnswerLiteralManager* AnswerLiteralManager::getInstance()
{
  CALL("AnswerLiteralManager::getInstance");

  static AnswerLiteralManager instance;

  return &instance;
}

bool AnswerLiteralManager::tryGetAnswer(Clause* refutation, Stack<TermList>& answer)
{
  CALL("AnswerLiteralManager::tryGetAnswer");

  RCClauseStack::Iterator cit(_answers);
  while(cit.hasNext()) {
    Clause* ansCl = cit.next();
    if(ansCl->length()!=1) {
      continue;
    }
    Literal* lit = (*ansCl)[0];
    unsigned arity = lit->arity();
    for(unsigned i=0; i<arity; i++) {
      answer.push(*lit->nthArgument(i));
    }
    return true;
  }
  return false;
}

Literal* AnswerLiteralManager::getAnswerLiteral(VList* vars,Formula* f)
{
  CALL("AnswerLiteralManager::getAnswerLiteral");

  static Stack<TermList> litArgs;
  litArgs.reset();
  VList::Iterator vit(vars);
  TermStack sorts;
  while(vit.hasNext()) {
    unsigned var = vit.next();
    TermList sort;
    if(SortHelper::tryGetVariableSort(var,f,sort)){
      sorts.push(sort);
      litArgs.push(TermList(var, false));
    }
  }

  unsigned vcnt = litArgs.size();
  unsigned pred = env.signature->addFreshPredicate(vcnt,"ans");
  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  predSym->setType(OperatorType::getPredicateType(sorts.size(), sorts.begin()));
  predSym->markAnswerPredicate();
  return Literal::create(pred, vcnt, true, false, litArgs.begin());
}

Unit* AnswerLiteralManager::tryAddingAnswerLiteral(Unit* unit)
{
  CALL("AnswerLiteralManager::tryAddingAnswerLiteral");

  if(unit->isClause() || unit->inputType()!=UnitInputType::CONJECTURE) {
    return unit;
  }

  FormulaUnit* fu = static_cast<FormulaUnit*>(unit);
  Formula* form = fu->formula();

  if(form->connective()!=NOT || form->uarg()->connective()!=EXISTS) {
    return unit;
  }

  Formula* quant =form->uarg();
  VList* vars = quant->vars();
  ASS(vars);

  FormulaList* conjArgs = 0;
  FormulaList::push(quant->qarg(), conjArgs);
  Literal* ansLit = getAnswerLiteral(vars,quant);
  FormulaList::push(new AtomicFormula(ansLit), conjArgs);

  Formula* conj = new JunctionFormula(AND, conjArgs);
  Formula* newQuant = new QuantifiedFormula(EXISTS, vars, 0,conj);
  Formula* newForm = new NegatedFormula(newQuant);

  newForm = Flattening::flatten(newForm);

  Unit* res = new FormulaUnit(newForm,FormulaTransformation(InferenceRule::ANSWER_LITERAL, unit));

  return res;
}

void AnswerLiteralManager::addAnswerLiterals(Problem& prb)
{
  CALL("AnswerLiteralManager::addAnswerLiterals");

  if(addAnswerLiterals(prb.units())) {
    prb.invalidateProperty();
  }
}

/**
 * Attempt adding answer literals into questions among the units
 * in the list @c units. Return true is some answer literal was added.
 */
bool AnswerLiteralManager::addAnswerLiterals(UnitList*& units)
{
  CALL("AnswerLiteralManager::addAnswerLiterals");

  bool someAdded = false;
  UnitList::DelIterator uit(units);
  while(uit.hasNext()) {
    Unit* u = uit.next();
    Unit* newU = tryAddingAnswerLiteral(u);
    if(u!=newU) {
      someAdded = true;
      uit.replace(newU);
    }
  }
  return someAdded;
}

bool AnswerLiteralManager::isAnswerLiteral(Literal* lit)
{
  CALL("AnswerLiteralManager::isAnswerLiteral");

  unsigned pred = lit->functor();
  Signature::Symbol* sym = env.signature->getPredicate(pred);
  return sym->answerPredicate();
}
bool AnswerLiteralManager::isAnswerClause(Clause* cl,bool ignoreSplits)
{
  CALL("AnswerLiteralManager::isAnswerClause");

  if(!ignoreSplits && !cl->noSplits()) {
    return false;
  }

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    if(!isAnswerLiteral((*cl)[i])) {
      return false;
    }
  }
  return true;
}


void AnswerLiteralManager::print()
{
  env.beginOutput();
  env.out() << "% SZS answers Tuple [";
  RCClauseStack::Iterator cit(_answers);
  while(cit.hasNext()) {
    Clause* ansCl = cit.next();
    if(ansCl->length()>1){ env.out() << "("; }

      for(unsigned i=0;i<ansCl->length();i++){
      env.out() << "[";
      Literal* lit = (*ansCl)[i];
        for(unsigned j=0;j<lit->arity();j++){
          TermList aLit = (*lit->nthArgument(j));

    // try evaluating aLit
    if(aLit.isTerm()){
      InterpretedLiteralEvaluator eval;
      unsigned p = env.signature->addFreshPredicate(1,"p");
      unsigned sort = SortHelper::getResultSort(aLit.term());
      OperatorType* type = OperatorType::getPredicateType({sort});
      env.signature->getPredicate(p)->setType(type);
      Literal* l = Literal::create1(p,true,aLit);
      Literal* res =0;
      bool constant, constTrue;
      Stack<Literal*> sideConditions;
      bool litMod = eval.evaluate(l,constant,res,constTrue,sideConditions);
      if(litMod && res && sideConditions.isEmpty()){
        aLit.setTerm(res->nthArgument(0)->term());
      }
    }

    env.out() << aLit.toString();

          if(j+1 < lit->arity()){
            env.out() << ',';
          }
        }
        env.out() << "]";
        if(i+1 < ansCl->length()){
          env.out() << '|';
        }
      }
    if(ansCl->length()>1){env.out() << ")";} 
    if(cit.hasNext()){ env.out() << ",";}
  }
  env.out() << "|_] for " << env.options->problemName() << endl;
  env.endOutput();
}

void AnswerLiteralManager::onNewClause(Clause* cl)
{
  CALL("AnswerLiteralManager::onNewClause");

  if(!isAnswerClause(cl)){ return; }

  _answers.push(cl);

  static unsigned qc = env.options->questionCount();
  if(qc > 0 && _answers.size() >= qc){ 
    print();
    System::terminateImmediately(1);
  }

  Clause* refutation = getRefutation(cl);

  //throw MainLoop::RefutationFoundException(refutation);

/*
  env.beginOutput();
  env.out()<<cl->toString()<<endl;
  env.endOutput();
*/
}

Clause* AnswerLiteralManager::getResolverClause(unsigned pred)
{
  CALL("AnswerLiteralManager::getResolverClause");

  Clause* res;
  if(_resolverClauses.find(pred, res)) {
    return res;
  }

  static Stack<TermList> args;
  args.reset();

  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  ASS(predSym->answerPredicate());
  unsigned arity = predSym->arity();

  for(unsigned i=0; i<arity; i++) {
    args.push(TermList(i, false));
  }
  Literal* lit = Literal::create(pred, arity, true, false, args.begin());
  res = Clause::fromIterator(getSingletonIterator(lit),NonspecificInference0(UnitInputType::AXIOM,InferenceRule::ANSWER_LITERAL_RESOLVER));

  _resolverClauses.insert(pred, res);
  return res;
}

Clause* AnswerLiteralManager::getRefutation(Clause* answer)
{
  CALL("AnswerLiteralManager::getRefutation");

  unsigned clen = answer->length();
  UnitList* premises = 0;
  UnitList::push(answer, premises);

  for(unsigned i=0; i<clen; i++) {
    Clause* resolvingPrem = getResolverClause((*answer)[i]->functor());
    UnitList::push(resolvingPrem, premises);
  }

  Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(),
      GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, premises));
  return refutation;
}

}










