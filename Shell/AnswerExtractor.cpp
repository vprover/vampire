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

void AnswerExtractor::tryOutputAnswer(Clause* refutation)
{
  CALL("AnswerExtractor::tryOutputAnswer");

  Stack<TermList> answer;

  bool alm = true;
  if(!AnswerLiteralManager::getInstance()->tryGetAnswer(refutation, answer)) {
    alm = false;
    ConjunctionGoalAnswerExractor cge;
    if(!cge.tryGetAnswer(refutation, answer)) {
      return;
    }
  }
  env.beginOutput();
  if (alm) AnswerLiteralManager::getInstance()->tryOutputInputUnits();
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

void AnswerExtractor::tryOutputInputUnits() {
  if (!UnitList::isEmpty(_inputs)) {
    env.out() << "% Inputs for question answering:" << endl;
    UnitList::Iterator it(_inputs);
    while (it.hasNext()) {
      env.out() << it.next()->toString() << endl;
    }
  }
}

void AnswerExtractor::getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits)
{
  CALL("AnswerExtractor::getNeededUnits");

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
  CALL("AnswerLiteralManager::getInstance");

  static AnswerLiteralManager instance;

  return &instance;
}

bool AnswerLiteralManager::tryGetAnswer(Clause* refutation, Stack<TermList>& answer)
{
  CALL("AnswerLiteralManager::tryGetAnswer");

  //RCClauseStack::Iterator cit(_answers);
  //while(cit.hasNext()) {
  //  Clause* ansCl = cit.next();
  //  if(ansCl->length()!=1) {
  //    continue;
  //  }
  //  Literal* lit = (*ansCl)[0];
  //  unsigned arity = lit->arity();
  //  for(unsigned i=0; i<arity; i++) {
  //    answer.push(_skolemReplacement.transformTermList(*lit->nthArgument(i), env.signature->getPredicate(lit->functor())->predType()->arg(i)));
  //  }
  //  return true;
  //}
  //return false;

  // TODO(hzzv): move the following to a separate class and uncomment code above
  ASS((_lastAnsLit || List<pair<Clause*, Literal*>>::isNonEmpty(_answerPairs)));
  if (_lastAnsLit) {
    List<pair<Clause*, Literal*>>::push(make_pair(nullptr, _lastAnsLit), _answerPairs);
  }

  ClauseStack premiseClauses;
  Stack<Unit*> conjectures;
  DHSet<Unit*> proofUnits;
  getNeededUnits(refutation, premiseClauses, conjectures, proofUnits);

  List<pair<Clause*, Literal*>>::Iterator it(_answerPairs);
  ALWAYS(it.hasNext());
  pair<Clause*, Literal*> p = it.next();
  unsigned arity = p.second->arity();
  Stack<TermList> sorts(arity);
  for (unsigned i = 0; i < arity; i++) {
    sorts.push(env.signature->getPredicate(p.second->functor())->predType()->arg(i));
    answer.push(_skolemReplacement.transformTermList(*p.second->nthArgument(i), sorts[i]));
  }
  while(it.hasNext()) {
    p = it.next();
    ASS(p.first != nullptr);
    if (!proofUnits.contains(p.first)) {
      continue;
    }
    // Create the condition for an if-then-else by negating the clause
    Formula* condition = getConditionFromClause(p.first);
    for (unsigned i = 0; i < arity; i++) {
      ASS_EQ(sorts[i], env.signature->getPredicate(p.second->functor())->predType()->arg(i));
      // Construct the answer by nesting an if-then-else
      answer[i] = TermList(Term::createITE(condition, _skolemReplacement.transformTermList(*p.second->nthArgument(i), sorts[i]), answer[i], sorts[i]));
    }
  }
  return true;
}

void AnswerLiteralManager::bindSkolemToVar(Term* skolem, unsigned var) {
  ASS(env.signature->getFunction(skolem->functor())->skolem());
  _skolemReplacement.bindSkolemToVar(skolem, var);
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

  if(form->connective()!=NOT ||
      (form->uarg()->connective()!=EXISTS &&
        (env.options->questionAnswering() == Options::QuestionAnsweringMode::ANSWER_LITERAL ||
         form->uarg()->connective()!=FORALL || form->uarg()->qarg()->connective()!=EXISTS))) {
    return unit;
  }

  //Unit* u = unit;
  //while (u->derivedFromInput() && u->inference().rule() != InferenceRule::INPUT) {
  //  Inference::Iterator it = unit->inference().iterator();
  //  Unit* newu = u;
  //  while (u->inference().hasNext(it) && newu->inference().rule() != InferenceRule::INPUT) {
  //    newu = u->inference().next(it);
  //    ASS(!newu->derivedFromInput() || !newu->inference().hasNext(it));
  //  }
  //  if (newu == u) break;
  //  u = newu;
  //}
  //if (u->inference().rule() == InferenceRule::INPUT) UnitList::push(u, _inputs);
  Formula* quant = (form->uarg()->connective()==EXISTS) ? form->uarg() : form->uarg()->qarg();
  VList* vars = quant->vars();
  ASS(vars);

  FormulaList* conjArgs = 0;
  FormulaList::push(quant->qarg(), conjArgs);
  Literal* ansLit = getAnswerLiteral(vars,quant);
  FormulaList::push(new AtomicFormula(ansLit), conjArgs);

  Formula* conj = new JunctionFormula(AND, conjArgs);
  Formula* newQuant = new QuantifiedFormula(EXISTS, vars, 0,conj);
  if (form->uarg()->connective()!=EXISTS) newQuant = new QuantifiedFormula(FORALL, form->uarg()->vars(), 0, newQuant);
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

void AnswerLiteralManager::onNewClause(Clause* cl)
{
  CALL("AnswerLiteralManager::onNewClause");

  if(!cl->noSplits() || cl->isEmpty()) {
    return;
  }

  unsigned clen = cl->length();
  for(unsigned i=0; i<clen; i++) {
    if(!(*cl)[i]->isAnswerLiteral()) {
      return;
    }
  }

  // TODO(hzzv): move the method to a derived class and uncomment the following line in this class
  //_answers.push(cl);
  
  ASS(cl->hasAnswerLiteral())
  _lastAnsLit = cl->getAnswerLiteral();
  Clause* refutation = getRefutation(cl);
  throw MainLoop::RefutationFoundException(refutation);
}

Clause* AnswerLiteralManager::recordAnswerAndReduce(Clause* cl) {
  CALL("AnswerLiteralManager::recordAnswerAndReduce");

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
    if ((*cl)[i] != ansLit) (*newCl)[idx++] = (*cl)[i];
  }
  if (!removeDefaultAnsLit) {
    List<pair<Clause*, Literal*>>::push(make_pair(newCl, ansLit), _answerPairs);
  } else {
    _lastAnsLit = ansLit;
  }
  return newCl;
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

Literal* AnswerLiteralManager::makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) {
  CALL("AnswerLiteralManager::makeITEAnswerLiteral");

  ASS(Literal::headersMatch(thenLit, elseLit, /*complementary=*/false));

  Signature::Symbol* predSym = env.signature->getPredicate(thenLit->functor());
  Stack<TermList> litArgs;
  Term* condTerm = Term::createFromLiteral(condition);
  // TODO(hzzv): using special-term-ITEs:
  //Literal* cond = qr.substitution->applyToQuery(queryLit);
  for (unsigned i = 0; i < thenLit->arity(); ++i) {
    TermList* ttl = thenLit->nthArgument(i);
    TermList* etl = elseLit->nthArgument(i);
    // TODO(hzzv): maybe unify variables if they do not occur anywhere else in the clause?
    if (ttl == etl) litArgs.push(*ttl);
    else {
      // TODO(hzzv): using special-term-ITEs:
      //litArgs.push(TermList(Term::createITE(new Kernel::AtomicFormula(cond), *dtl, *ctl, predSym->predType()->arg(i))));
      litArgs.push(TermList(Term::createRegularITE(condTerm, *ttl, *etl, predSym->predType()->arg(i))));
    }
  }
  return Literal::create(thenLit->functor(), thenLit->arity(), thenLit->polarity(), /*commutative=*/false, litArgs.begin());
}

Formula* AnswerLiteralManager::getConditionFromClause(Clause* cl) {
  CALL("AnswerLiteralManager::getConditionFromClause");

  FormulaList* fl = FormulaList::empty();
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* newLit = Literal::complementaryLiteral(_skolemReplacement.transform((*cl)[i]));
    FormulaList::push(new AtomicFormula(newLit), fl);
  }
  return JunctionFormula::generalJunction(Connective::AND, fl);
}

void AnswerLiteralManager::ConjectureSkolemReplacement::bindSkolemToVar(Term* t, unsigned v) {
  ASS(_skolemToVar.count(t) == 0);
  _skolemToVar[t] = v;
}

TermList AnswerLiteralManager::ConjectureSkolemReplacement::transformTermList(TermList tl, TermList sort) {
  CALL("AnswerLiteralManager::ConjectureSkolemReplacement::transformTermList");
  // First replace free variables by 0
  if (tl.isVar() || (tl.isTerm() && !tl.term()->ground())) {
    TermList zero(theory->representConstant(IntegerConstantType(0)));
    if (tl.isVar()) {
      if (sort == AtomicSort::intSort()) return zero;
      else {
        vstring name = "cz_" + sort.toString();
        unsigned czfn;
        if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
          czfn = env.signature->addFreshFunction(0, name.c_str());
          env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
        } 
        TermList res(Term::createConstant(czfn));
        return res;
      }
    } else {
      Substitution s;
      vset<unsigned> done;
      Kernel::VariableWithSortIterator vit(tl.term());
      while (vit.hasNext()) {
        pair<TermList, TermList> p = vit.next();
        unsigned v = p.first.var();
        TermList& vsort = p.second;
        if (done.count(v) == 0) {
          done.insert(v);
          if (vsort == AtomicSort::intSort()) s.bind(v, zero);
          else {
            vstring name = "cz_" + vsort.toString();
            unsigned czfn;
            if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
              czfn = env.signature->addFreshFunction(0, name.c_str());
              env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
            } 
            TermList res(Term::createConstant(czfn));
            s.bind(v, res);
          }
        }
      }
      tl = TermList(tl.term()->apply(s));
    }
  }
  // Then replace skolems by variables
  return transform(tl);
  //TermList transformed = transformSubterm(tl);
  //if (transformed != tl) return transformed;
  //else return transform(tl);
}

TermList AnswerLiteralManager::ConjectureSkolemReplacement::transform(TermList tl) {
  TermList transformed = transformSubterm(tl);
  if (transformed != tl) return transformed;
  else return TermTransformer::transform(tl);
}

TermList AnswerLiteralManager::ConjectureSkolemReplacement::transformSubterm(TermList trm) {
  if (trm.isTerm()) {
    auto it = _skolemToVar.find(trm.term());
    if (it != _skolemToVar.end()) return TermList(it->second, false);
  }
  return trm;
}

}










