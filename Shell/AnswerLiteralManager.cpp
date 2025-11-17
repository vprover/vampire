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
 * @file AnswerLiteralManager.cpp
 * Implements class AnswerLiteralManager.
 */

#include <set>

#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "Lib/StringUtils.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Options.hpp"

#include "Parse/TPTP.hpp"

#include "AnswerLiteralManager.hpp"

static bool isProperAnswerClause(Clause* cl) {
  static bool ground_only = (env.options->questionAnswering() == Options::QuestionAnsweringMode::PLAIN) && (env.options->questionAnsweringGroundOnly());

  return !cl->isEmpty() && forAll(cl->iterLits(),[] (Literal* l) { return l->isAnswerLiteral() && (!ground_only || l->ground()); } );
}

namespace Inferences
{

Clause* AnswerLiteralResolver::simplify(Clause* cl)
{
  if (isProperAnswerClause(cl)) {
    return AnswerLiteralManager::getInstance()->getRefutation(cl);
  }
  return cl;
}

}


namespace Shell
{

using namespace std;
typedef List<pair<unsigned,pair<Clause*, Literal*>>> AnsList;

///////////////////////
// AnswerLiteralManager
//

AnswerLiteralManager* AnswerLiteralManager::getInstance()
{
  static AnswerLiteralManager* instance =
    (env.options->questionAnswering() == Options::QuestionAnsweringMode::PLAIN) ?
      static_cast<AnswerLiteralManager*>(new PlainALManager()) :
      ((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS) ?
        static_cast<AnswerLiteralManager*>(new SynthesisALManager()) :
        nullptr);

  return instance;
}

void AnswerLiteralManager::addAnswerLiterals(Problem& prb)
{
  if(addAnswerLiterals(prb.units())) {
    prb.invalidateProperty();
  }
}

/**
 * Attempt adding answer literals into questions among the units
 * in the list @c units. Return true if some answer literal was added.
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

Unit* AnswerLiteralManager::tryAddingAnswerLiteral(Unit* unit)
{
  if (unit->isClause() || (unit->inputType()!=UnitInputType::CONJECTURE && unit->inputType()!=UnitInputType::NEGATED_CONJECTURE)) {
    return unit; // do nothing
  }

  Formula* topF = static_cast<FormulaUnit*>(unit)->formula();

  // it must start with a not
  if(topF->connective()!=NOT) {
    return unit; // do nothing
  }

  Formula* subNot = topF->uarg();

  bool skolemise = false;
  Formula* eQuant;
  if (subNot->connective() == EXISTS) {
    eQuant = subNot;
  } else if (subNot->connective() == FORALL) {
    skolemise = true;
    Formula* subForall = subNot->qarg();
    if (subForall->connective() == EXISTS) {
      eQuant = subForall;
    } else {
      return unit; // do nothing
    }
  } else {
    return unit; // do nothing
  }

  VList* eVars = eQuant->vars();
  SList* eSrts = eQuant->sorts();
  ASS(eVars);

  FormulaList* conjArgs = 0;
  FormulaList::push(eQuant->qarg(), conjArgs);
  Literal* ansLit = getAnswerLiteral(eVars,eSrts,eQuant);
  _originUnitsAndInjectedLiterals.insert(ansLit->functor(),make_pair(unit,ansLit));
  FormulaList::push(new AtomicFormula(ansLit), conjArgs);

  Formula* out = new NegatedFormula(new QuantifiedFormula(EXISTS, eVars, eSrts, new JunctionFormula(AND, conjArgs)));

  if (skolemise) {
    Map<unsigned,std::string>* questionVars = Parse::TPTP::findQuestionVars(unit->number());

    VList* fVars = subNot->vars();
    SList* fSrts = subNot->sorts();
    Substitution subst;
    while (VList::isNonEmpty(fVars)) {
      unsigned var = fVars->head();
      fVars = fVars->tail();
      unsigned skFun = env.signature->addSkolemFunction(/*arity=*/0, /*suffix=*/"in");
      Signature::Symbol* skSym = env.signature->getFunction(skFun);
      if ((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS)) {
        ALWAYS(static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->addIntroducedComputableSymbol(make_pair(skFun, /*isPredicate=*/false)));
      }
      TermList sort;
      if (SList::isNonEmpty(fSrts)) {
        sort = fSrts->head();
        fSrts = fSrts->tail();
      } else if (!SortHelper::tryGetVariableSort(var, subNot, sort)) {
        sort = AtomicSort::defaultSort();
      }
      OperatorType* ot = OperatorType::getConstantsType(sort);
      skSym->setType(ot);
      Term* skTerm = Term::create(skFun, /*arity=*/0, /*args=*/nullptr);
      subst.bindUnbound(var, skTerm);
      recordSkolemBinding(skTerm, var, questionVars ? questionVars->get(var) : TermList(var,false).toString() );
    }
    out = SubstHelper::apply(out, subst);
  }

  return new FormulaUnit(out, FormulaClauseTransformation(skolemise ? InferenceRule::ANSWER_LITERAL_INPUT_SKOLEMISATION : InferenceRule::ANSWER_LITERAL_INJECTION, unit));
}

TermList AnswerLiteralManager::possiblyEvaluateAnswerTerm(TermList aT)
{
  if(aT.isTerm() && !aT.term()->isSpecial()){
    InterpretedLiteralEvaluator eval;
    unsigned p = env.signature->addFreshPredicate(1,"p");
    TermList sort = SortHelper::getResultSort(aT.term());
    OperatorType* type = OperatorType::getPredicateType({sort});
    env.signature->getPredicate(p)->setType(type);
    Literal* l = Literal::create1(p,true,aT);
    Literal* res =0;
    bool constant, constTrue;
    bool litMod = eval.evaluate(l,constant,res,constTrue);
    if(litMod && res){
      aT.setTerm(res->nthArgument(0)->term());
    }
  }
  return aT;
}

void AnswerLiteralManager::tryOutputAnswer(Clause* refutation, std::ostream& out)
{
  Stack<Clause*> answer;

  if (!tryGetAnswer(refutation, answer)) {
    return;
  }

  DHSet<unsigned> seenSkolems;

  out << "% SZS answers Tuple [";

  std::stringstream vss;
  optionalAnswerPrefix(vss);
  if (answer.size() > 1) {
    vss << "(";
  }
  Stack<Clause*>::BottomFirstIterator aIt(answer);
  while(aIt.hasNext()) {
    Clause* aCl = aIt.next();
    if (closeFreeVariablesForPrinting()) {
      auto varIt = aCl->getVariableIterator();
      if (varIt.hasNext()) {
        vss << "∀";
        while(varIt.hasNext()) {
          vss << TermList(varIt.next(),false).toString();
          if (varIt.hasNext()) {
            vss << ",";
          }
        }
        vss << ".";
      }
    }
    if (aCl->size() > 1) {
      vss << "(";
    }
    auto lIt = aCl->iterLits();
    while (lIt.hasNext()) {
      Literal* aLit = lIt.next();
      vss << "[";
      unsigned arity = aLit->arity();

      Map<unsigned,std::string>* questionVars = 0;
      std::pair<Unit*,Literal*> unitAndLiteral;
      if (_originUnitsAndInjectedLiterals.find(aLit->functor(),unitAndLiteral)) {
        questionVars = Parse::TPTP::findQuestionVars(unitAndLiteral.first->number());
      }

      for(unsigned i=0; i<arity; i++) {
        if(i > 0) {
          vss << ',';
        }
        if (questionVars) {
          vss << questionVars->get(unitAndLiteral.second->nthArgument(i)->var()) << "->";
        }
        TermList evalauted = possiblyEvaluateAnswerTerm(*aLit->nthArgument(i));
        if (evalauted.isTerm()){ // just check which Skolems we might have used
          NonVariableNonTypeIterator it(evalauted.term(),/*includeSelf=*/true);
          while (it.hasNext()) {
            unsigned f = it.next()->functor();
            std::pair<unsigned,Unit*> dummy;
            if (_skolemsOrigin.find(f,dummy)) {
              seenSkolems.insert(f);
            }
          }
        }
        vss << evalauted;
      }
      vss << "]";
      if(lIt.hasNext()) {
        vss << "|";
      }
    }
    if (aCl->size() > 1) {
      vss << ")";
    }
    if(aIt.hasNext()) {
      vss << "|";
    }
  }
  if (answer.size() > 1) {
    vss << ")";
  }
  out << postprocessAnswerString(vss.str());
  out << "|_] for " << env.options->problemName() << endl;

  // recall what the skolems mean:
  DHSet<unsigned>::Iterator it(seenSkolems);
  while (it.hasNext()) {
    unsigned f = it.next();
    const std::pair<unsigned,Unit*>& origin = _skolemsOrigin.get(f);
    out << "%    " << env.signature->getFunction(f)->name() << " introduced for " << TermList(origin.first,false).toString() << " in " << origin.second->toString() << endl;
  }
}

static bool pushFirstPremiseToAnswerIfFromResolver(Inference& inf, Stack<Clause*>& answer)
{
  if (inf.rule() == InferenceRule::UNIT_RESULTING_RESOLUTION) {
    auto it = inf.iterator();
    ASS(inf.hasNext(it));
    Clause* firstParent = inf.next(it)->asClause();
    // cout << firstParent->toNiceString() << endl;
    if (isProperAnswerClause(firstParent)) {
      answer.push(firstParent);
      return true;
    }
  }
  return false;
}

bool AnswerLiteralManager::tryGetAnswer(Clause* refutation, Stack<Clause*>& answer)
{
  ASS(refutation->isEmpty());

  Inference& inf = refutation->inference();
  if (pushFirstPremiseToAnswerIfFromResolver(inf,answer)) {
    return true;
  } else if (inf.rule() == InferenceRule::AVATAR_REFUTATION) {
    bool added = false;
    auto it = inf.iterator();
    while (inf.hasNext(it)) {
      Unit* prem = inf.next(it);
      Inference& inf2 = prem->inference();
      if (inf2.rule() == InferenceRule::AVATAR_CONTRADICTION_CLAUSE) {
        auto it2 = inf2.iterator();
        Unit* anEmpty = inf2.next(it2);
        ASS(!inf2.hasNext(it2));
        Inference& inf3 = anEmpty->inference();
        added |= pushFirstPremiseToAnswerIfFromResolver(inf3,answer);
      }
    }
    return added;
  }
  // currently does nothing for AVATAR_REFUTATION_SMT (which does not get minimized)

  return false;
}

Literal* AnswerLiteralManager::getAnswerLiteral(VList* vars,SList* srts,Formula* f)
{
  static Stack<TermList> litArgs;
  litArgs.reset();
  TermStack sorts;
  while(VList::isNonEmpty(vars)) {
    unsigned var = vars->head();
    vars = vars->tail();
    TermList sort;
    if (SList::isNonEmpty(srts)) {
      sort = srts->head();
      srts = srts->tail();
    } else if(!SortHelper::tryGetVariableSort(var, f, sort)) {
      sort = AtomicSort::defaultSort();
    }
    litArgs.push(TermList(var, false));
    sorts.push(sort);
  }

  unsigned vcnt = litArgs.size();
  unsigned pred = env.signature->addFreshPredicate(vcnt,"ans");
  Signature::Symbol* predSym = env.signature->getPredicate(pred);
  predSym->setType(OperatorType::getPredicateType(sorts.size(), sorts.begin()));
  predSym->markAnswerPredicate();
  // don't need equality proxy for answer literals
  predSym->markSkipCongruence();
  if ((env.options->questionAnswering() == Options::QuestionAnsweringMode::SYNTHESIS)) {
    ALWAYS(static_cast<Shell::SynthesisALManager*>(Shell::SynthesisALManager::getInstance())->addIntroducedComputableSymbol(make_pair(pred, /*isPredicate=*/true)));
  }
  return Literal::create(pred, vcnt, true, litArgs.begin());
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
  Literal* lit = Literal::create(pred, arity, true, args.begin());
  res = Clause::fromIterator(getSingletonIterator(lit),NonspecificInference0(UnitInputType::AXIOM,InferenceRule::ANSWER_LITERAL_RESOLVER));

  _resolverClauses.insert(pred, res);
  return res;
}

Clause* AnswerLiteralManager::getRefutation(Clause* answer)
{
  unsigned clen = answer->length();
  UnitList* premises = 0;

  for(unsigned i=0; i<clen; i++) {
    Clause* resolvingPrem = getResolverClause((*answer)[i]->functor());
    UnitList::push(resolvingPrem, premises);
  }

  // finally, put in the actual answer clause (for an easier retrieval later)
  UnitList::push(answer, premises);

  Clause* refutation = Clause::fromIterator(LiteralIterator::getEmpty(),
      GeneratingInferenceMany(InferenceRule::UNIT_RESULTING_RESOLUTION, premises));
  return refutation;
}

///////////////////////
// PlainALManager
//

void PlainALManager::recordSkolemBinding(Term* skT,unsigned var,std::string vName)
{
  _skolemNames.push(std::make_pair(skT,vName));
}

void PlainALManager::optionalAnswerPrefix(std::ostream& out)
{
  if(!_skolemNames.isEmpty()) {
    out << "λ";
    auto it =  _skolemNames.iterFifo();
    while (it.hasNext()) {
      out << it.next().first->toString();
      if (it.hasNext())
        out << ",";
    }
    out << ".";
  }
}

std::string PlainALManager::postprocessAnswerString(std::string answer)
{
  /** string replacement is not ideal:
   * - substrings elsewhere could be rewritten (not just the intended skolems)
   * - also, if the users chooses a unfortunate variable names
   *   (with the "question" role, the TPTP parser is storing the original names for us)
   *   new clashes might arise
   *
   * However, creating a symbol which looks like a variable
   * (but is not, since vampire's variables are just unsigneds n, printed as "X<n>")
   * and starts with an uppercase character (not allowed for anything else than variables in TPTP)
   * sounded like too much pain.
  */

  auto it =  _skolemNames.iter();
  while (it.hasNext()) {
    auto [skT,vName] = it.next();
    std::string to;
    Lib::StringUtils::replaceAll(answer,skT->toString(),vName);
  }
  return answer;
}

///////////////////////
// SynthesisALManager
//

void SynthesisALManager::getNeededUnits(Clause* refutation, ClauseStack& premiseClauses, Stack<Unit*>& conjectures, DHSet<Unit*>& allProofUnits)
{
  Stack<Unit*> toDo;
  toDo.push(refutation);

  while(toDo.isNonEmpty()) {
    Unit* curr = toDo.pop();
    if(!allProofUnits.insert(curr)) {
      continue;
    }
    Inference& inf = curr->inference();
    InferenceRule infRule = inf.rule();
    if(infRule==InferenceRule::NEGATED_CONJECTURE) {
      conjectures.push(curr);
    }
    if(infRule==InferenceRule::CLAUSIFY ||
	    (curr->isClause() && (infRule==InferenceRule::INPUT || infRule==InferenceRule::NEGATED_CONJECTURE )) ){
      ASS(curr->isClause());
      premiseClauses.push(curr->asClause());
    }
    auto it = inf.iterator();
    while(inf.hasNext(it)) {
      Unit* premise = inf.next(it);
      toDo.push(premise);
    }
  }
}

void SynthesisALManager::recordSkolemBinding(Term* skTerm, unsigned var, std::string)
{
  // TODO(hzzv): use the var name
  _skolemReplacement.bindSkolemToTermList(skTerm, TermList(var, false));
}

bool SynthesisALManager::tryGetAnswer(Clause* refutation, Stack<Clause*>& answer)
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

  // We iterate through the stored _answerPairs. An answer pair p is relevant if:
  // - either it is the _lastAnsLit (i.e., has p.first==0)
  // - or it corresponds to a clause contained in the proof (i.e., proofNums.contains(p.first))
  // We construct an answer by nesting if-then-elses, using as the then-branch the current
  // answer pair, and as the else-branch the program constructed so far.
  AnsList::Iterator it(_answerPairs);
  ALWAYS(it.hasNext());
  pair<unsigned, pair<Clause*, Literal*>> p = it.next();
  while (p.first > 0 && !proofNums.contains(p.first) && it.hasNext()) p = it.next();
  ASS(p.first == 0 || proofNums.contains(p.first));
  // The first relevant answer literal:
  Literal* origLit = p.second.second;
  unsigned arity = origLit->arity();
  Stack<TermList> answerArgs(arity);
  Stack<TermList> sorts(arity);
  // Initialization: each answer is set to the answer from origLit.
  for (unsigned i = 0; i < arity; i++) {
    sorts.push(env.signature->getPredicate(origLit->functor())->predType()->arg(i));
    answerArgs.push(_skolemReplacement.transformTermList(*origLit->nthArgument(i), sorts[i]));
  }
  // Go through all other answer pairs and use the relevant ones.
  while(it.hasNext()) {
    p = it.next();
    ASS(p.second.first != nullptr);
    if (!proofNums.contains(p.first)) {
      continue;
    }
    ASS_EQ(p.first, p.second.first->number());
    // Create the condition for an if-then-else by negating the clause
    Formula* condition = getConditionFromClause(p.second.first);
    for (unsigned i = 0; i < arity; i++) {
      ASS_EQ(sorts[i], env.signature->getPredicate(p.second.second->functor())->predType()->arg(i));
      // Construct the answer using if-then-else
      answerArgs[i] = TermList(Term::createITE(condition, _skolemReplacement.transformTermList(*p.second.second->nthArgument(i), sorts[i]), answerArgs[i], sorts[i]));
    }
  }
  // just a single literal answer
  answer.push(Clause::fromLiterals({Literal::create(origLit,answerArgs.begin())}, NonspecificInference0(UnitInputType::AXIOM,InferenceRule::INPUT)));

  outputRecursiveFunctions();

  return true;
}

void SynthesisALManager::onNewClause(Clause* cl)
{
  if(!cl->noSplits() || cl->isEmpty() || (cl->length() != 1) || !(*cl)[0]->isAnswerLiteral()) {
    return;
  }

  ASS(cl->hasAnswerLiteral())

  Literal* lit = cl->getAnswerLiteral();
  if (!isComputableOrVar(lit))
    return;
  _lastAnsLit = lit;

  Clause* refutation = getRefutation(cl);
  throw MainLoop::RefutationFoundException(refutation);
}

Clause* SynthesisALManager::recordAnswerAndReduce(Clause* cl) {
  if (!cl->noSplits() || !cl->hasAnswerLiteral() || !isComputable(cl)) {
    return nullptr;
  }
  // Check if the answer literal has only distinct variables as arguments.
  // If yes, we do not need to record the clause, because the answer literal
  // represents any answer.
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

  RStack<Literal*> resLits;
  for (Literal* curr : cl->iterLits()) {
    if (curr != ansLit) {
      resLits->push(curr);
    }
  }
  auto newCl = Clause::fromStack(*resLits,
      Inference(SimplifyingInference1(InferenceRule::ANSWER_LITERAL_REMOVAL, cl)));
  if (!removeDefaultAnsLit) {
    AnsList::push(make_pair(newCl->number(), make_pair(newCl, ansLit)), _answerPairs);
  } else {
    _lastAnsLit = ansLit;
  }
  return newCl;
}

Literal* SynthesisALManager::makeITEAnswerLiteral(Literal* condition, Literal* thenLit, Literal* elseLit) {
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
  return Literal::create(thenLit->functor(), thenLit->arity(), thenLit->polarity(), litArgs.begin());
}

void SynthesisALManager::pushEqualityConstraints(LiteralStack* ls, Literal* thenLit, Literal* elseLit) {
  ASS_EQ(thenLit->functor(), elseLit->functor());
  for (unsigned i = 0; i < thenLit->arity(); ++i) {
    TermList& t = *thenLit->nthArgument(i);
    TermList& e = *elseLit->nthArgument(i);
    if (t != e) {
      ls->push(Literal::createEquality(false, t, e, env.signature->getPredicate(thenLit->functor())->predType()->arg(i)));
    }
  }
}

Formula* SynthesisALManager::getConditionFromClause(Clause* cl) {
  FormulaList* fl = FormulaList::empty();
  for (unsigned i = 0; i < cl->length(); ++i) {
    Literal* newLit = Literal::complementaryLiteral(_skolemReplacement.transformLiteral((*cl)[i]));
    FormulaList::push(new AtomicFormula(newLit), fl);
  }
  return JunctionFormula::generalJunction(Connective::AND, fl);
}

/** Create a new complex term, with its top-level function symbol
 *  created as a dummy symbol representing the predicate of @b l, and copy
 *  from the array @b args its arguments. Insert it into the sharing
 *  structure if all arguments are shared.
 */
Term* SynthesisALManager::translateToSynthesisConditionTerm(Literal* l)
{
  ASS_EQ(l->getPreDataSize(), 0);
  ASS(!l->isSpecial());

  unsigned arity = l->arity();
  std::string fnName = "cond_";
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
      if (isPredicateComputable(l->functor())) {
        ALWAYS(_introducedComputable.insert(make_pair(fn, /*isPredicate=*/false)));
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
Term* SynthesisALManager::createRegularITE(Term* condition, TermList thenBranch, TermList elseBranch, TermList branchSort)
{
  unsigned itefn = getITEFunctionSymbol(branchSort);
  return Term::create(itefn, {TermList(condition), thenBranch, elseBranch});
}

void SynthesisALManager::ConjectureSkolemReplacement::bindSkolemToTermList(Term* t, TermList&& tl) {
  ASS(!_skolemToTermList.find(t));
  if (static_cast<SynthesisALManager*>(SynthesisALManager::getInstance())->isFunctionComputable(t->functor())) {
    ++_numInputSkolems;
  }
  _skolemToTermList.insert(t, std::move(tl));
}

TermList getConstantForVariable(TermList sort) {
  static TermList zero(theory->representConstant(IntegerConstantType(0)));
  if (sort == AtomicSort::intSort()) {
    return zero;
  } else {
    std::string name = "cz_" + sort.toString();
    unsigned czfn;
    if (!env.signature->tryGetFunctionNumber(name, 0, czfn)) {
      czfn = env.signature->addFreshFunction(0, name.c_str());
      env.signature->getFunction(czfn)->setType(OperatorType::getConstantsType(sort));
    } 
    return TermList(Term::createConstant(czfn));
  }
}

TermList SynthesisALManager::ConjectureSkolemReplacement::transformTermList(TermList tl, TermList sort) {
  // First replace free variables by 0-like constants
  if (tl.isVar() || (tl.isTerm() && !tl.term()->ground())) {
    if (tl.isVar()) {
      return getConstantForVariable(sort);
    } else {
      Substitution s;
      std::set<unsigned> done;
      Kernel::VariableWithSortIterator vit(tl.term());
      while (vit.hasNext()) {
        pair<TermList, TermList> p = vit.next();
        unsigned v = p.first.var();
        TermList& vsort = p.second;
        if (done.count(v) == 0) {
          done.insert(v);
          s.bindUnbound(v, getConstantForVariable(vsort));
        }
      }
      tl = TermList(tl.term()->apply(s));
    }
  }
  // Then replace skolems by variables
  return transformSubterm(transform(tl));
}

TermList SynthesisALManager::ConjectureSkolemReplacement::transformSubterm(TermList trm) {
  if (trm.isTerm()) {
    TermList* res = _skolemToTermList.findPtr(trm.term());
    if (res) {
      return *res;
    }
    Term* t = trm.term();
    unsigned functor = t->functor();
    if (static_cast<SynthesisALManager*>(SynthesisALManager::getInstance())->isRecTerm(t)) {
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
                TermList& c = (*fptr)->_cases[j];
                if (c.isTerm()) {
                  (*fptr)->_cases[j] = TermList(ssr.transform(c.term()));
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
      if (t->functor() == static_cast<SynthesisALManager*>(SynthesisALManager::getInstance())->getITEFunctionSymbol(sort)) {
        // Build condition
        Term* tcond = t->nthArgument(0)->term();
        std::string condName = tcond->functionName();
        unsigned pred = _condFnToPred.get(tcond->functor());
        Literal* newCond;
        if (env.signature->isEqualityPredicate(pred)) {
          newCond = Literal::createEquality(/*polarity=*/true, *tcond->nthArgument(0), *tcond->nthArgument(1), sort);
        } else {
          newCond = Literal::createFromIter(pred, /*polarity=*/true, anyArgIter(tcond));
        }
        // Build the whole ITE term
        return TermList(Term::createITE(new AtomicFormula(newCond), *(t->nthArgument(1)), *(t->nthArgument(2)), sort));
      }
    }
  }
  return trm;
}

void SynthesisALManager::ConjectureSkolemReplacement::outputRecursiveFunctions() {
  VirtualIterator<Function*> it = _functions.range();
  if (it.hasNext()) {
    cout << "% Recursive function definitions:" << endl;
    do {
      cout << it.next()->toString();
    } while (it.hasNext());
  }
}

SynthesisALManager::ConjectureSkolemReplacement::Function::Function(unsigned recFunctor, ConjectureSkolemReplacement* replacement) {
  // Store the heads of each case of the new function
  _caseHeads = replacement->_functionHeads->findPtr(recFunctor);
  ASS(_caseHeads);
  _cases.ensure(_caseHeads->size());
  // Add the new function to signature
  OperatorType* ot = env.signature->getFunction(recFunctor)->fnType();
  TermList in = ot->arg(ot->arity()-1);
  TermList out = ot->arg(0);
  ASS_EQ(env.signature->getTermAlgebraOfSort(in)->nConstructors(), _caseHeads->size());
  _functor = env.signature->addFreshFunction(/*arity=*/1, "rf");
  Signature::Symbol* f = env.signature->getFunction(_functor);
  f->setType(OperatorType::getFunctionType({in}, out));
  // Process SkolemTrackers corresponding to this function:
  // populate the maps mapping skolems to terms they represent.
  DHMap<Term*, TermList>* caseMap;
  const DHMap<unsigned, SkolemTracker>& mapping = replacement->_recursionMappings->get(recFunctor);
  DHMap<unsigned, SkolemTracker>::Iterator it(mapping);
  while (it.hasNext()) {
    unsigned var;
    SkolemTracker& st = it.nextRef(var);
    ASS_EQ(var, st.binding.first);
    ASS(!_skolemToTermList.find(st.binding.second));
    TermList tl(st.recursiveCall ? TermList(Term::create1(_functor, *(*_caseHeads)[st.constructorId]->nthArgument(st.indexInConstructor))) : TermList(var, false));
    _skolemToTermList.insert(st.binding.second, tl);
    _skolemToTermListForCase.getValuePtr(st.constructorId, caseMap);
    caseMap->insert(st.binding.second, tl);
  }
}

void SynthesisALManager::ConjectureSkolemReplacement::Function::addCases(Term* t) {
  ASS(_cases.size() == t->arity()-1);
  for (unsigned i = 0; i < t->arity()-1; ++i) {
    _cases[i] = *t->nthArgument(i);
  }
}

void SynthesisALManager::printSkolemTrackers() {
  cout << "Skolem mappings:" << endl;
  DHMap<unsigned, SkolemTracker*>::Iterator it(_skolemTrackers);
  while (it.hasNext()) {
    SkolemTracker* st = it.next();
    cout << st->toString() << endl;
  }
}

void SynthesisALManager::printRecursionMappings() {
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

void SynthesisALManager::registerSkolemSymbols(Term* recTerm, const Substitution& subst, const std::vector<Term*>& functionHeadsByConstruction, vector<SkolemTracker>& incompleteTrackers, const VList* us) {
  unsigned recFnId = recTerm->functor();
  unsigned ctorNumber = recTerm->arity()-1;
  ASS_EQ(ctorNumber, VList::length(us));
  ASS_EQ(ctorNumber, functionHeadsByConstruction.size());
  // Find out what is the order of arguments in `recTerm`, and
  // store the function heads in the correct indices in `_functionHeads`.
  // Each of the first `ctorNumber` argumentsi of the `recTerm` should be one of `us`.
  // The order of `us` is reverse to both the order of elements in `functionHeadsByConstruction`,
  // and to the `constructorId` of the SkolemTrackers.
  DArray<unsigned> ctorOrder(ctorNumber);
  vector<Term*> functionHeads(ctorNumber);
  VList::Iterator vit(us);
  unsigned i = 0;
  while (vit.hasNext()) {
    unsigned v = vit.next();
    DEBUG_CODE(bool found = false;)
    for (unsigned j = 0; j < ctorNumber; ++j) {
      TermList& arg = *(recTerm->nthArgument(j));
      ASS(arg.isVar());
      if (arg.var() == v) {
        ctorOrder[ctorNumber-i-1] = j;
        functionHeads[j] = functionHeadsByConstruction[ctorNumber-i-1];
        ++i;
        DEBUG_CODE(found = true;)
        break;
      }
    }
    ASS(found);
  }
  ALWAYS(_functionHeads.insert(recFnId, std::move(functionHeads)));

  // Finalize SkolemTrackers and store them.
  DHMap<unsigned, SkolemTracker>* mapping;
  ALWAYS(_recursionMappings.getValuePtr(recFnId, mapping));
  for (SkolemTracker& st : incompleteTrackers) {
    ASS_EQ(st.binding.second, nullptr);
    ASS_EQ(st.recFnId, 0);
    const unsigned var = st.binding.first;
    st.binding.second = subst.apply(var).term();
    st.recFnId = recFnId;
    st.constructorId = ctorOrder[st.constructorId];
    SkolemTracker* stp;
    ALWAYS(mapping->getValuePtr(var, stp, st));
    _skolemTrackers.insert(st.binding.second->functor(), stp);
  }
}

bool SynthesisALManager::isRecTerm(const Term* t) const {
  return (_recursionMappings.findPtr(t->functor()) != nullptr);
}

const SkolemTracker* SynthesisALManager::getSkolemTracker(unsigned skolemFunctor) const {
  return _skolemTrackers.get(skolemFunctor, nullptr);
}

bool SynthesisALManager::hasRecTerm(Literal* lit) {
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

bool SynthesisALManager::isFunctionComputable(unsigned functor) const {
  Signature::Symbol* s = env.signature->getFunction(functor);
  return (s->introduced() && _introducedComputable.contains(make_pair(functor, false))) ||
    (!s->introduced() && !_annotatedUncomputable.contains(make_pair(functor, false)));
}

bool SynthesisALManager::isPredicateComputable(unsigned functor) const {
  Signature::Symbol* s = env.signature->getPredicate(functor);
  return (s->introduced() && _introducedComputable.contains(make_pair(functor, true))) ||
    (!s->introduced() && !_annotatedUncomputable.contains(make_pair(functor, true)));
}

bool SynthesisALManager::computableOrVarHelper(const Term* t, DHMap<unsigned, unsigned>* recAncestors) const {
  ASS(t);
  unsigned f = t->functor();
  Signature::Symbol* symbol = env.signature->getFunction(f);

  if (!isFunctionComputable(f)) {
    // either an uncomputable symbol from the input, or an introduced symbol
    if (!symbol->skolem()) { // computability of skolems depends on the context, all else is really uncomputable
      return false;
    }
    if (!isRecTerm(t)) { // non-rec skolem terms need to be specifically allowed
      const Shell::SkolemTracker* st = getSkolemTracker(f);
      if (st == nullptr) {
         return false;
      }
      unsigned idx = 0;
      if (!recAncestors->find(st->recFnId, idx) || (idx != st->constructorId)) {
        return false;
      }
      return true;
    }
  }

  // Top functor is computable, now recurse.
  unsigned* idx = nullptr;
  if (isRecTerm(t)) {
    if (!recAncestors->getValuePtr(f, idx, -1)) {
      // TODO: investigate if we need to deal with answer literal in which
      // nested rec-term (of the same rec-function) occurs in some special way.
      // E.g., maybe we can replace "ans(rec(X0,rec(X1,sK2,X2),X3))"
      // by "X0 != X1 | sK2 != rec(X1,sK2,X2) | ans(rec(X0,sK2,X3))"
      return false;
    }
  }
  for (unsigned i = 0; i < t->numTermArguments(); i++) {
    const TermList tl = t->termArg(i);
    if (tl.isTerm()) { // else we have a variable, which needs no check
      if (idx) {
        *idx = i;
      }
      if (!computableOrVarHelper(tl.term(), recAncestors)) {
        return false;
      }
    }
  }
  if (idx) {
    recAncestors->remove(f);
  }

  return true;
}

bool SynthesisALManager::isComputableOrVar(const Term* t) const {
  DHMap<unsigned, unsigned> recAncestors;
  return computableOrVarHelper(t, &recAncestors);
}

bool SynthesisALManager::isComputableOrVar(const Literal* l) const {
  if (!isPredicateComputable(l->functor())) {
    return false;
  }
  for (unsigned i = 0; i < l->arity(); ++i) {
    const TermList* t = l->nthArgument(i);
    if (t->isTerm() && !isComputableOrVar(t->term())) {
      return false;
    }
  }
  return true;
}

bool SynthesisALManager::isComputable(const Clause* c) const {
  for (const Literal* l : c->iterLits()) {
    if (l->isAnswerLiteral()) {
      continue;
    }
    if (!isComputable(l)) {
      return false;
    }
  }
  return true;
}

}
