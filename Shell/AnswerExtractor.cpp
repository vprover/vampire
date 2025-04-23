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

#include "Kernel/Signature.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
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

using namespace std;
typedef List<pair<unsigned,pair<Clause*, Literal*>>> AnsList;

void AnswerExtractor::tryOutputAnswer(Clause* refutation)
{
  Stack<TermList> answer;

  bool hasSynthManager = false;
  if (SynthesisManager::getInstance()->tryGetAnswer(refutation, answer)) {
    hasSynthManager = true;
  } else if (!AnswerLiteralManager::getInstance()->tryGetAnswer(refutation, answer)) {
    ConjunctionGoalAnswerExractor cge;
    if(!cge.tryGetAnswer(refutation, answer)) {
      return;
    }
  }
  env.beginOutput();
  if (hasSynthManager) {
    SynthesisManager::getInstance()->tryOutputInputUnits();
    SynthesisManager::getInstance()->outputRecursiveFunctions();
  }
  env.out() << "% SZS answers Tuple [[";
  Stack<TermList>::BottomFirstIterator ait(answer);
  while(ait.hasNext()) {
    TermList aLit = ait.next();
    // try evaluating aLit (only if not special)
    if(aLit.isTerm() && !aLit.term()->isSpecial()){
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

void AnswerExtractor::getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits)
{
  InferenceStore& is = *InferenceStore::instance();

  Stack<Unit*> toDo;
  toDo.push(refutation);

  while(toDo.isNonEmpty()) {
    Unit* curr = toDo.pop();
    if(!allProofUnits.insert(curr)) {
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
    for(unsigned i=0; i<_goalCnt; i++) {
      _btData[i].drop();
    }
  }

  bool run()
  {
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
    _unifIts[_depth] = _lemmas.getUnifications(_goalLits[_depth], false, false);
    _triedEqUnif[_depth] = false;
    _subst.bdRecord(_btData[_depth]);
  }
  void leaveGoal()
  {
    _subst.bdDone();
    _btData[_depth].backtrack();
  }
  bool nextGoalUnif()
  {
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
  ClauseStack premiseClauses;
  Stack<Unit*> conjectures;
  DHSet<Unit*> all;
  getNeededUnits(refutation, premiseClauses, conjectures, all);

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
  static AnswerLiteralManager instance;

  return &instance;
}

bool AnswerLiteralManager::tryGetAnswer(Clause* refutation, Stack<TermList>& answer)
{
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
  // don't need equality proxy for answer literals
  predSym->markSkipCongruence();
  return Literal::create(pred, vcnt, true, false, litArgs.begin());
}

Unit* AnswerLiteralManager::tryAddingAnswerLiteral(Unit* unit)
{
  Formula* quant = tryGetQuantifiedFormulaForAnswerLiteral(unit);
  if (quant == nullptr) {
    return unit;
  }

  addInputUnit(unit);

  VList* vars = quant->vars();
  ASS(vars);

  FormulaList* conjArgs = 0;
  FormulaList::push(quant->qarg(), conjArgs);
  Literal* ansLit = getAnswerLiteral(vars,quant);
  FormulaList::push(new AtomicFormula(ansLit), conjArgs);

  Formula* conj = new JunctionFormula(AND, conjArgs);
  return createUnitFromConjunctionWithAnswerLiteral(conj, vars, unit);
}

Formula* AnswerLiteralManager::tryGetQuantifiedFormulaForAnswerLiteral(Unit* unit) {
  if (unit->isClause() || unit->inputType()!=UnitInputType::CONJECTURE) {
    return nullptr;
  }

  Formula* form = static_cast<FormulaUnit*>(unit)->formula();

  if (form->connective()!=NOT || form->uarg()->connective()!=EXISTS) {
    return nullptr;
  }

  return form->uarg();
}

Unit* AnswerLiteralManager::createUnitFromConjunctionWithAnswerLiteral(Formula* junction, VList* existsVars, Unit* originalUnit) {
  Formula* f = Flattening::flatten(new NegatedFormula(new QuantifiedFormula(EXISTS, existsVars, 0, junction)));
  return new FormulaUnit(f, FormulaTransformation(InferenceRule::ANSWER_LITERAL, originalUnit));
}

void AnswerLiteralManager::addAnswerLiterals(Problem& prb)
{
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

void AnswerLiteralManager::onNewClause(Clause* cl)
{
  if(!cl->noSplits()) {
    return;
  }

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    Literal* lit = (*cl)[i];
    if(!lit->isAnswerLiteral()) {
      return;
    }
  }

  _answers.push(cl);
  
  Clause* refutation = getRefutation(cl);
  throw MainLoop::RefutationFoundException(refutation);
}

Clause* AnswerLiteralManager::getResolverClause(unsigned pred)
{
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

SynthesisManager* SynthesisManager::getInstance()
{
  static SynthesisManager instance;

  return &instance;
}

bool SynthesisManager::tryGetAnswer(Clause* refutation, Stack<TermList>& answer)
{
  if (!_lastAnsLit && AnsList::isEmpty(_answerPairs)) {
    return false;
  }
  if (_lastAnsLit) {
    AnsList::push(make_pair(0, make_pair(nullptr, _lastAnsLit)), _answerPairs);
  }

  _skolemReplacement.associateRecMappings(&_recursionMappings, &_functionHeads);

  ClauseStack premiseClauses;
  Stack<Unit*> conjectures;
  DHSet<Unit*> proofUnits;
  getNeededUnits(refutation, premiseClauses, conjectures, proofUnits);
  DHSet<unsigned> proofNums;
  DHSet<Unit*>::Iterator puit(proofUnits);
  while (puit.hasNext()) proofNums.insert(puit.next()->number());

  AnsList::Iterator it(_answerPairs);
  ALWAYS(it.hasNext());
  pair<unsigned, pair<Clause*, Literal*>> p = it.next();
  while (p.first > 0 && !proofNums.contains(p.first) && it.hasNext()) p = it.next();
  ASS(p.first == 0 || proofNums.contains(p.first));
  unsigned arity = p.second.second->arity();
  Stack<TermList> sorts(arity);
  for (unsigned i = 0; i < arity; i++) {
    sorts.push(env.signature->getPredicate(p.second.second->functor())->predType()->arg(i));
    answer.push(_skolemReplacement.transformTermList(*p.second.second->nthArgument(i), sorts[i]));
  }
  while(it.hasNext()) {
    p = it.next();
    ASS(p.second.first != nullptr);
    ASS(p.first == p.second.first->number());
    if (!proofNums.contains(p.first)) {
      continue;
    }
    // Create the condition for an if-then-else by negating the clause
    Formula* condition = getConditionFromClause(p.second.first);
    for (unsigned i = 0; i < arity; i++) {
      ASS_EQ(sorts[i], env.signature->getPredicate(p.second.second->functor())->predType()->arg(i));
      // Construct the answer using if-then-else
      answer[i] = TermList(Term::createITE(condition, _skolemReplacement.transformTermList(*p.second.second->nthArgument(i), sorts[i]), answer[i], sorts[i]));
    }
  }
  return true;
}

void SynthesisManager::tryOutputInputUnits() {
  if (!UnitList::isEmpty(_inputs)) {
    env.out() << "% Inputs for synthesis:" << endl;
    UnitList::Iterator it(_inputs);
    while (it.hasNext()) {
      env.out() << it.next()->toString() << endl;
    }
  }
}

void SynthesisManager::onNewClause(Clause* cl)
{
  if(!cl->noSplits() || cl->isEmpty() || (cl->length() != 1) || !(*cl)[0]->isAnswerLiteral()) {
    return;
  }

  ASS(cl->hasAnswerLiteral())

  Literal* lit = cl->getAnswerLiteral();
  if (!lit->computableOrVar())
    return;
  _lastAnsLit = lit;

  Clause* refutation = getRefutation(cl);
  throw MainLoop::RefutationFoundException(refutation);
}

Clause* SynthesisManager::recordAnswerAndReduce(Clause* cl) {
  if (!cl->noSplits() || !cl->hasAnswerLiteral() || !cl->computable()) {
    return nullptr;
  }
  // Check if the answer literal has only distinct variables as arguments.
  // If yes, we do not need to record the clause, because the answer literal
  // represents any answer.
  unsigned clen = cl->length();
  bool removeDefaultAnsLit = true;
  Literal* ansLit = cl->getAnswerLiteral();
  Set<unsigned> vars;
  for (unsigned i = 0; i < ansLit->numTermArguments(); ++i) {
    TermList* tl = ansLit->nthArgument(i);
    if (!tl->isVar()) {
      removeDefaultAnsLit = false;
      break;
    }
    vars.insert(tl->var());
  }
  if (vars.size() != ansLit->numTermArguments()) {
    removeDefaultAnsLit = false;
  }

  unsigned nonAnsLits = 0;
  for(unsigned i=0; i<clen; i++) {
    if((*cl)[i] != ansLit) {
      nonAnsLits++;
    }
  }
  ASS_EQ(nonAnsLits, clen-1);

  Inference inf(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_REMOVAL, cl));
  Clause* newCl = new(nonAnsLits) Clause(nonAnsLits, inf);
  unsigned idx = 0;
  for (unsigned i = 0; i < clen; i++) {
    if ((*cl)[i] != ansLit) {
      (*newCl)[idx++] = (*cl)[i];
    }
  }
  if (!removeDefaultAnsLit) {
    AnsList::push(make_pair(newCl->number(), make_pair(newCl, ansLit)), _answerPairs);
  } else {
    _lastAnsLit = ansLit;
  }
  return newCl;
}

Literal* SynthesisManager::makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) {
  ASS(Literal::headersMatch(thenLit, elseLit, /*complementary=*/false));

  Signature::Symbol* predSym = env.signature->getPredicate(thenLit->functor());
  Stack<TermList> litArgs;
  Term* condTerm = translateToSynthesisConditionTerm(condition);
  for (unsigned i = 0; i < thenLit->arity(); ++i) {
    TermList* ttl = thenLit->nthArgument(i);
    TermList* etl = elseLit->nthArgument(i);
    if (ttl == etl) {
      litArgs.push(*ttl);
    } else {
      litArgs.push(TermList(createRegularITE(condTerm, *ttl, *etl, predSym->predType()->arg(i))));
    }
  }
  return Literal::create(thenLit->functor(), thenLit->arity(), thenLit->polarity(), /*commutative=*/false, litArgs.begin());
}

Formula* SynthesisManager::tryGetQuantifiedFormulaForAnswerLiteral(Unit* unit) {
  if(unit->isClause() || (unit->inputType()!=UnitInputType::CONJECTURE && unit->inputType()!=UnitInputType::NEGATED_CONJECTURE)) {
    return nullptr;
  }

  Formula* form = static_cast<FormulaUnit*>(unit)->formula();

  if(form->connective()!=NOT ||
      (form->uarg()->connective()!=EXISTS &&
        (env.options->questionAnswering() == Options::QuestionAnsweringMode::ANSWER_LITERAL ||
         form->uarg()->connective()!=FORALL || form->uarg()->qarg()->connective()!=EXISTS))) {
    return nullptr;
  }



  return (form->uarg()->connective()==EXISTS) ? form->uarg() : form->uarg()->qarg();
}

Unit* SynthesisManager::createUnitFromConjunctionWithAnswerLiteral(Formula* junction, VList* existsVars, Unit* originalUnit) {
  Formula* form = static_cast<FormulaUnit*>(originalUnit)->formula();
  Formula* quant = new QuantifiedFormula(FORALL, existsVars, 0, new NegatedFormula(junction));
  bool skolemise = (form->uarg()->connective()==FORALL);
  if (skolemise) {
    VList::Iterator it(form->uarg()->vars());
    Substitution subst;
    while (it.hasNext()) {
      unsigned var = it.next();
      unsigned skFun = env.signature->addSkolemFunction(/*arity=*/0, /*suffix=*/"in", /*computable=*/true);
      Signature::Symbol* skSym = env.signature->getFunction(skFun);
      TermList sort;
      if (!SortHelper::tryGetVariableSort(var, form, sort)) {
        sort = AtomicSort::defaultSort();
      }
      OperatorType* ot = OperatorType::getConstantsType(sort); 
      skSym->setType(ot);
      Term* skTerm = Term::create(skFun, /*arity=*/0, /*args=*/nullptr);
      subst.bind(var, skTerm);
      _skolemReplacement.bindSkolemToTermList(skTerm, TermList(var, false));
    }
    quant = SubstHelper::apply(quant, subst);
  }
  quant = Flattening::flatten(quant);
  return new FormulaUnit(quant, FormulaTransformation(skolemise ? InferenceRule::ANSWER_LITERAL_INPUT_SKOLEMISATION : InferenceRule::ANSWER_LITERAL, originalUnit));
}

Formula* SynthesisManager::getConditionFromClause(Clause* cl) {
  FormulaList* fl = FormulaList::empty();
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* newLit = Literal::complementaryLiteral(_skolemReplacement.transform((*cl)[i]));
    FormulaList::push(new AtomicFormula(newLit), fl);
  }
  return JunctionFormula::generalJunction(Connective::AND, fl);
}

/** Create a new complex term, with its top-level function symbol
 *  created as a dummy symbol representing the predicate of @b l, and copy
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure if all arguments are shared.
 */
Term* SynthesisManager::translateToSynthesisConditionTerm(Literal* l)
{
  ASS_EQ(l->getPreDataSize(), 0);
  ASS(!l->isSpecial());

  unsigned arity = l->arity();
  vstring fnName = "cond_";
  if (l->isNegative()) {
    fnName.append("not_");
  }
  fnName.append(l->predicateName());
  if (l->isEquality()) {
    fnName.append(SortHelper::getEqualityArgumentSort(l).toString());
  }
  bool added = false;
  unsigned fn = env.signature->addFunction(fnName, arity, added);
  // Store the mapping between the function and predicate symbols
  _skolemReplacement.addCondPair(fn, l->functor());
  if (added) {
    Signature::Symbol* sym = env.signature->getFunction(fn);
    Stack<TermList> argSorts;
    if (l->isEquality()) {
      TermList as = SortHelper::getEqualityArgumentSort(l);
      argSorts.push(as);
      argSorts.push(as);
    } else {
      OperatorType* ot = env.signature->getPredicate(l->functor())->predType();
      for (unsigned i = 0; i < arity; ++i) {
        argSorts.push(ot->arg(i));
      }
      if (!env.signature->getPredicate(l->functor())->computable()) {
        sym->markUncomputable();
      }
    }
    sym->setType(OperatorType::getFunctionType(arity, argSorts.begin(), AtomicSort::defaultSort()));
  }
  
  Stack<TermList> args;
  for (unsigned i = 0; i < arity; ++i) {
    args.push(*(l->nthArgument(i)));
  }
  return Term::create(fn, arity, args.begin());
}

/**
 * Create a (condition ? thenBranch : elseBranch) expression
 * and return the resulting term
 */
Term* SynthesisManager::createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort)
{
  unsigned itefn = getITEFunctionSymbol(branchSort);
  return Term::create(itefn, {TermList(condition), thenBranch, elseBranch});
}

void SynthesisManager::ConjectureSkolemReplacement::bindSkolemToTermList(Term* t, TermList&& tl) {
  ASS(!_skolemToTermList.find(t));
  if (env.signature->getFunction(t->functor())->computable()) {
    ++_numInputSkolems;
  }
  _skolemToTermList.emplace(t, std::move(tl));
}

TermList getConstantForVariable(TermList sort) {
  static TermList zero(theory->representConstant(IntegerConstantType(0)));
  if (sort == AtomicSort::intSort()) {
    return zero;
  } else {
    vstring name = "cz_" + sort.toString();
    unsigned czfn;
    if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
      czfn = env.signature->addFreshFunction(0, name.c_str());
      env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
    } 
    return TermList(Term::createConstant(czfn));
  }
}

TermList SynthesisManager::ConjectureSkolemReplacement::transformTermList(TermList tl, TermList sort) {
  // First replace free variables by 0-like constants
  if (tl.isVar() || (tl.isTerm() && !tl.term()->ground())) {
    TermList zero(theory->representConstant(IntegerConstantType(0)));
    if (tl.isVar()) {
      return getConstantForVariable(sort);
    } else {
      Substitution s;
      vset<unsigned> done;
      Kernel::VariableWithSortIterator vit(tl.term());
      while (vit.hasNext()) {
        pair<TermList, TermList> p = vit.next();
        unsigned v = p.first.var();
        if (done.count(v) == 0) {
          done.insert(v);
          TermList rep = getConstantForVariable(p.second);
          s.bind(v, rep);
        }
      }
      tl = TermList(tl.term()->apply(s));
    }
  }
  // Then replace skolems by variables
  return transform(tl);
}

TermList SynthesisManager::ConjectureSkolemReplacement::transformSubterm(TermList trm) {
  if (trm.isTerm()) {
    TermList* res = _skolemToTermList.findPtr(trm.term());
    if (res) {
      return *res;
    }
    Term* t = trm.term();
    unsigned functor = t->functor();
    if (SynthesisManager::getInstance()->isRecTerm(t)) {
      // Construct a new recursive function corresponding to 'trm'.
      ASS(_recursionMappings->find(functor));
      Function* recf = new Function(functor, this);
      SimpleSkolemReplacement ssr(&recf->_skolemToTermList);
      Term* transformed = ssr.transform(t);
      recf->addCases(transformed);
      // If the cases of the recursive function contain other recursive functions,
      // their definitions might need skolem replacement corresponding to this function.
      for (unsigned i = 0; i < transformed->arity()-1; ++i) {
        // Iterate over cases and replace only the associated skolems in each.
        TermList* narg = transformed->nthArgument(i);
        DHMap<Term*, TermList>* m = recf->_skolemToTermListForCase.findPtr(i);
        if (narg->isTerm() && m) {
          ssr.setMap(m);
          NonVariableIterator it(narg->term());
          while (it.hasNext()) {
            TermList tl = it.next();
            ASS(tl.isTerm());
            Function** fptr = _functions.findPtr(tl.term()->functor());
            if (fptr) {
              for (unsigned j = 0; j < (*fptr)->_cases.size(); ++j) {
                TermList& t = (*fptr)->_cases[j];
                if (t.isTerm()) {
                  (*fptr)->_cases[j] = TermList(ssr.transform(t.term()));
                }
              }
            }
          }
        }
      }
      unsigned rfunctor = recf->_functor;
      _functions.insert(rfunctor, recf);
      // Replace 'trm' by the function called on the last argument of this 'trm'.
      return TermList(Term::create(rfunctor, {*t->nthArgument(t->arity()-1)}));
    } else if ((t->arity() == 3) && t->nthArgument(0)->isTerm()) {
      TermList sort = env.signature->getFunction(functor)->fnType()->arg(1);
      if (functor == getITEFunctionSymbol(sort)) {
        // Build condition
        Term* tcond = t->nthArgument(0)->term();
        vstring condName = tcond->functionName();
        unsigned pred = _condFnToPred.get(tcond->functor());
        Literal* newCond;
        if (env.signature->isEqualityPredicate(pred)) {
          newCond = Literal::createEquality(/*polarity=*/true, *tcond->nthArgument(0), *tcond->nthArgument(1), sort);
        } else {
          newCond = Literal::create(pred, tcond->arity(), /*polarity=*/true, /*commutative=*/false, tcond->args());
        }
        // Build the whole ITE term
        return TermList(Term::createITE(new AtomicFormula(newCond), *(t->nthArgument(1)), *(t->nthArgument(2)), sort));
      }
    }
  }
  return trm;
}

void SynthesisManager::ConjectureSkolemReplacement::outputRecursiveFunctions() {
  VirtualIterator<Function*> it = _functions.range();
  if (it.hasNext()) {
    env.out() << "% Recursive function definitions:" << endl;
    do {
      env.out() << it.next()->toString();
    } while (it.hasNext());
  }
}

SynthesisManager::ConjectureSkolemReplacement::Function::Function(unsigned recFunctor, ConjectureSkolemReplacement* replacement) {
  _caseHeads = replacement->_functionHeads->findPtr(recFunctor);
  ASS(_caseHeads);
  _cases.ensure(_caseHeads->size());
  const DHMap<unsigned, SkolemTracker>& mapping = replacement->_recursionMappings->get(recFunctor);
  OperatorType* ot = env.signature->getFunction(recFunctor)->fnType();
  TermList in = ot->arg(ot->arity()-1);
  TermList out = ot->arg(0);
  ASS(env.signature->getTermAlgebraOfSort(in)->nConstructors() == _caseHeads->size());
  _functor = env.signature->addFreshFunction(/*arity=*/1, "rf");
  Signature::Symbol* f = env.signature->getFunction(_functor);
  f->setType(OperatorType::getFunctionType({in}, out));
  DHMap<Term*, TermList>* caseMap;
  DHMap<unsigned, SkolemTracker>::Iterator it(mapping);
  while (it.hasNext()) {
    unsigned var;
    SkolemTracker& st = it.nextRef(var);
    ASS(var == st.binding.first);
    ASS(!_skolemToTermList.find(st.binding.second));
    TermList tl(st.recursiveCall ? TermList(Term::create1(_functor, *(*_caseHeads)[st.constructorId]->nthArgument(st.indexInConstructor))) : TermList(var, false));
    _skolemToTermList.insert(st.binding.second, tl);
    _skolemToTermListForCase.getValuePtr(st.constructorId, caseMap);
    caseMap->insert(st.binding.second, tl);
  }
}

void SynthesisManager::ConjectureSkolemReplacement::Function::addCases(Term* t) {
  ASS(_cases.size() == t->arity()-1);
  for (unsigned i = 0; i < t->arity()-1; ++i) {
    _cases[i] = *t->nthArgument(i);
  }
}

void SynthesisManager::registerRecSymbol(unsigned recFnId) {
  return;
  DHMap<unsigned, SkolemTracker>* mapping;
  ALWAYS(_recursionMappings.getValuePtr(recFnId, mapping));
}

void SynthesisManager::addInductionVarData(unsigned recFnId, unsigned var, unsigned consId, bool recCall, unsigned idxInCons) {
  return;
  DHMap<unsigned, SkolemTracker>* mapping = _recursionMappings.findPtr(recFnId);
  ASS(mapping != nullptr);
  ALWAYS(mapping->insert(var, SkolemTracker(Binding(var, nullptr), consId, recCall, idxInCons, recFnId)));
}

void SynthesisManager::printSkolemTrackers() {
  cout << "Skolem mappings:" << endl;
  DHMap<unsigned, SkolemTracker*>::Iterator it(_skolemTrackers);
  while (it.hasNext()) {
    SkolemTracker* st = it.next();
    cout << st->toString() << endl;
  }
}


void SynthesisManager::printRecursionMappings() {
  cout << "Recursion mappings:" << endl;
  RecursionMappings::Iterator rit(_recursionMappings);
  unsigned v;
  while (rit.hasNext()) {
    unsigned recFn;
    auto& m = rit.nextRef(recFn);
    cout << "  recFn " << recFn << ":" << endl; 
    DHMap<unsigned, SkolemTracker>::Iterator mit(m);
    while (mit.hasNext()) {
      SkolemTracker& s = mit.nextRef(v);
      cout << v << ": " << s.toString() << endl;
    }
  }
}

void SynthesisManager::registerSkolemSymbols(Term* recTerm, const DHMap<unsigned, Term*>& bindings, const List<Term*>* functionHeadsByConstruction, vector<SkolemTracker>& incompleteTrackers, const VList* us) {
  unsigned recFnId = recTerm->functor();
  unsigned ctorNumber = recTerm->arity()-1;
  ASS(ctorNumber == VList::length(us));
  ASS(ctorNumber == List<Term*>::length(functionHeadsByConstruction));
  // Find out what is the order of arguments in `recTerm`.
  // Each of the first `ctorNumber` arguments should be one of `us`.
  // The order of `us` is the same as the order of `functionHeadsByConstruction`,
  // and reverse to the `constructorId` of the SkolemTrackers.
  DArray<unsigned> ctorOrder(ctorNumber);
  VList::Iterator vit(us);
  unsigned i = 0;
  while (vit.hasNext()) {
    unsigned v = vit.next();
    bool found = false;
    for (unsigned j = 0; j < ctorNumber; ++j) {
      TermList& arg = *(recTerm->nthArgument(j));
      ASS(arg.isVar());
      if (arg.var() == v) {
        ctorOrder[ctorNumber-i-1] = j;
        ++i;
        found = true;
        break;
      }
    }
    ASS(found);
  }
  // Store `functionHeads` in the correct indices in `_functionHeads`.
  List<Term*>::Iterator fhit(functionHeadsByConstruction);
  i = 0;
  vector<Term*> functionHeads(ctorNumber);
  while (fhit.hasNext()) {
    functionHeads[ctorOrder[ctorNumber-i-1]] = fhit.next();
    ++i;
  }
  ALWAYS(_functionHeads.insert(recFnId, std::move(functionHeads)));

  // Finalize SkolemTrackers and store them.
  DHMap<unsigned, SkolemTracker>* mapping;
  ALWAYS(_recursionMappings.getValuePtr(recFnId, mapping));
  for (SkolemTracker& st : incompleteTrackers) {
    ASS(st.binding.second == nullptr);
    ASS(st.recFnId == 0);
    const unsigned var = st.binding.first;
    st.binding.second = bindings.get(var);
    st.recFnId = recFnId;
    st.constructorId = ctorOrder[st.constructorId];
    SkolemTracker* stp;
    ALWAYS(mapping->getValuePtr(var, stp, st));
    _skolemTrackers.insert(st.binding.second->functor(), stp);
  }
}

bool SynthesisManager::isRecTerm(const Term* t) {
  return (_recursionMappings.findPtr(t->functor()) != nullptr);
}

const SkolemTracker* SynthesisManager::getSkolemTracker(unsigned skolemFunctor) {
  return _skolemTrackers.get(skolemFunctor, nullptr);
}

bool SynthesisManager::hasRecTerm(Literal* lit) {
  NonVariableIterator it(lit);
  while (it.hasNext()) {
    TermList tl = it.next();
    ASS(tl.isTerm());
    if (isRecTerm(tl.term())) {
      return true;
    }
  }
  return false;
}

}
