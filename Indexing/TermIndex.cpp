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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"

#include "Inferences/InductionHelper.hpp"

#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "TermIndex.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

TermIndex::~TermIndex()
{
  delete _is;
}

TermQueryResultIterator TermIndex::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getUnifications(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getUnificationsUsingSorts(TermList t, TermList sort,
          bool retrieveSubstitutions)
{
  return _is->getUnificationsUsingSorts(t, sort, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getGeneralizations(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getInstances(t, retrieveSubstitutions);
}


void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti;
#if VHOL    
    if(!env.property->higherOrder()){
#endif
      rsti = EqHelper::getSubtermIterator(lit,_ord);
#if VHOL    
    } else {
      rsti = EqHelper::getFoSubtermIterator(lit,_ord);
    }
#endif
    while (rsti.hasNext()) {
      if (adding) {
        _is->insert(rsti.next(), lit, c);
      }
      else {
        _is->remove(rsti.next(), lit, c);
      }
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
}

template <class SubtermIterator>
void DemodulationSubtermIndex<SubtermIterator>::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE);

  static DHSet<TermList> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    // it is true (as stated below) that inserting only once per clause would be sufficient
    // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
    // so if the order changes while a clause is in the index (which can happen with "-sa otter")
    // the removes could be called on different literals than the inserts!
    inserted.reset();
    Literal* lit=(*c)[i];
    SubtermIterator it(lit);
    while (it.hasNext()) {
      TermList t=it.next();
      if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        it.right();
        continue;
      }
      if (adding) {
        _is->insert(t, lit, c);
      }
      else {
        _is->remove(t, lit, c);
      }
    }
  }
}

#if VHOL
template class DemodulationSubtermIndex<FirstOrderSubtermIt>;
#endif
template class DemodulationSubtermIndex<NonVariableNonTypeIterator>;

void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationLHSIndex::handleClause");

  if (c->length()!=1) {
    return;
  }

  TimeCounter tc(TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE);

  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt);
  while (lhsi.hasNext()) {
    if (adding) {
      _is->insert(lhsi.next(), lit, c);
    }
    else {
      _is->remove(lhsi.next(), lit, c);
    }
  }
}

void InductionTermIndex::handleClause(Clause* c, bool adding)
{
  CALL("InductionTermIndex::handleClause");

  TimeCounter tc(TC_INDUCTION_TERM_INDEX_MAINTENANCE);

  if (InductionHelper::isInductionClause(c)) {
  // Iterate through literals & check if the literal is suitable for induction
    for (unsigned i=0;i<c->length();i++) {
      Literal* lit = (*c)[i];
      if (InductionHelper::isInductionLiteral(lit)) {
        SubtermIterator it(lit);
        while (it.hasNext()) {
          TermList tl = it.next();
          if (!tl.term()) continue;
          // TODO: each term (and its subterms) should be processed
          // only once per literal, see DemodulationSubtermIndex
          if (InductionHelper::isInductionTermFunctor(tl.term()->functor()) &&
              InductionHelper::isIntInductionTermListInLiteral(tl, lit)) {
            if (adding) {
              _is->insert(tl, lit, c);
            } else {
              _is->remove(tl, lit, c);
            }
          }
        }
      }
    }
  }
}

void StructInductionTermIndex::handleClause(Clause* c, bool adding)
{
  CALL("StructInductionTermIndex::handleClause");

  if (!InductionHelper::isInductionClause(c)) {
    return;
  }
  static DHSet<TermList> inserted;
  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    inserted.reset();
    Literal* lit = (*c)[i];
    if (!lit->ground()) {
      continue;
    }
    SubtermIterator it(lit);
    while (it.hasNext()) {
      TermList tl = it.next();
      if (!inserted.insert(tl)) {
        it.right();
        continue;
      }
      ASS(tl.isTerm());
      if (InductionHelper::isInductionTermFunctor(tl.term()->functor()) &&
          InductionHelper::isStructInductionFunctor(tl.term()->functor())) {
        if (adding) {
          _is->insert(tl, lit, c);
        } else {
          _is->remove(tl, lit, c);
        }
      }
    }
  }
}


/////////////////////////////////////////////////////
// Indices for higher-order inferences from here on//
/////////////////////////////////////////////////////

void PrimitiveInstantiationIndex::populateIndex()
{
  CALL("PrimitiveInstantiationIndex::populateIndex");

  /*typedef ApplicativeHelper AH;

  static Options::PISet set = env.options->piSet();

  auto srtOf = [] (TermList t) {
    ASS(t.isTerm());
    return SortHelper::getResultSort(t.term());
  };

  static TermList boolS = AtomicSort::boolSort();

  TermList s1 = TermList(0, false);
  TermList x = TermList(1, false);
  TermList y = TermList(2, false);
  TermList s1_bool = AtomicSort::arrowSort(s1, boolS);
  TermList args1[] = {s1, boolS, boolS};
  TermList args2[] = {s1, s1_bool, s1_bool};

  unsigned k_comb = env.signature->getCombinator(Signature::K_COMB);
  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  unsigned v_and = env.signature->getBinaryProxy("vAND");
  unsigned v_or = env.signature->getBinaryProxy("vOR");
  unsigned v_imp = env.signature->getBinaryProxy("vIMP");
  unsigned v_not = env.signature->getNotProxy();
  unsigned v_equals = env.signature->getEqualityProxy();

  TermList kcomb = TermList(Term::create2(k_comb, AtomicSort::boolSort(), s1));
  TermList bcomb1 = TermList(Term::create(b_comb, 3, args1));
  TermList bcomb2 = TermList(Term::create(b_comb, 3, args2));
  TermList vand = TermList(Term::createConstant(v_and));
  TermList vor = TermList(Term::createConstant(v_or));
  TermList vimp = TermList(Term::createConstant(v_imp));
  TermList vnot = TermList(Term::createConstant(v_not));
  TermList vequals = TermList(Term::create1(v_equals, s1));

  TermList kTerm1 = AH::createAppTerm3(srtOf(kcomb), kcomb, TermList(Term::foolFalse()), x);
  TermList kTerm2 = AH::createAppTerm3(srtOf(kcomb), kcomb, TermList(Term::foolTrue()), x);
  TermList andTerm = AH::createAppTerm3(srtOf(vand), vand, x, y);
  TermList orTerm = AH::createAppTerm3(srtOf(vor), vor, x, y);
  TermList impTerm = AH::createAppTerm3(srtOf(vimp), vimp, x, y);
  TermList notTerm = AH::createAppTerm(srtOf(vnot), vnot, x);
  TermList equalsTerm = AH::createAppTerm3(srtOf(vequals), vequals, x, y);
  TermList trm = AH::createAppTerm(srtOf(bcomb1), bcomb1, vnot);
  TermList notEqualsTerm = AH::createAppTerm3(srtOf(bcomb2), bcomb2, trm, vequals);
  notEqualsTerm = AH::createAppTerm3(srtOf(notEqualsTerm), notEqualsTerm, x, y);

  if(set == Options::PISet::ALL){
    _is->insert(kTerm1, 0, 0);
    _is->insert(kTerm2, 0, 0);
    _is->insert(andTerm, 0, 0);
    _is->insert(orTerm, 0, 0);
    _is->insert(impTerm, 0, 0);
    _is->insert(notTerm, 0, 0);
    _is->insert(equalsTerm, 0, 0);
    _is->insert(notEqualsTerm, 0, 0);
  } else if (set == Options::PISet::ALL_EXCEPT_NOT_EQ){
    _is->insert(kTerm1, 0, 0);
    _is->insert(kTerm2, 0, 0);
    _is->insert(andTerm, 0, 0);
    _is->insert(orTerm, 0, 0);
    _is->insert(impTerm, 0, 0);
    _is->insert(notTerm, 0, 0);
    _is->insert(equalsTerm, 0, 0);
  } else if (set == Options::PISet::FALSE_TRUE_NOT){
    _is->insert(kTerm1, 0, 0);
    _is->insert(kTerm2, 0, 0);
    _is->insert(notTerm, 0, 0);
  } else if (set == Options::PISet::FALSE_TRUE_NOT_EQ_NOT_EQ){
    _is->insert(kTerm1, 0, 0);
    _is->insert(kTerm2, 0, 0);
    _is->insert(notTerm, 0, 0);
    _is->insert(equalsTerm, 0, 0);
    _is->insert(notEqualsTerm, 0, 0);
  }*/
}

void SkolemisingFormulaIndex::insertFormula(TermList formula, TermList skolem)
{
  CALL("SkolemisingFormulaIndex::insertFormula");
  _is->insert(formula, skolem);
}

/*void HeuristicInstantiationIndex::insertInstantiation(TermList sort, TermList instantiation)
{
  CALL("HeuristicInstantiationIndex::insertInstantiation");
  _is->insert(sort, instantiation);
}

void HeuristicInstantiationIndex::handleClause(Clause* c, bool adding)
{
  CALL("HeuristicInstantiationIndex::handleClause");

  typedef ApplicativeHelper AH;

  TermList freshVar(c->maxVar() + 1, false);
  VList* boundVar = new VList(freshVar.var());

  for (unsigned i=0; i<c->length(); i++) {
    Literal* lit=(*c)[i];
    TermList leftHead, rightHead, lhSort, rhSort;
    static TermStack leftArgs;
    static TermStack rightArgs;
    AH::getHeadSortAndArgs(*lit->nthArgument(0), leftHead, lhSort, leftArgs);
    AH::getHeadSortAndArgs(*lit->nthArgument(1), rightHead, rhSort, rightArgs);
    if(leftHead.isTerm() && AH::getComb(leftHead) == Signature::NOT_COMB &&
       AH::getProxy(leftHead) == Signature::NOT_PROXY &&
      leftHead == rightHead &&
      leftArgs.size() == rightArgs.size() &&
      leftArgs.size())
    {
      TermList sort, boundVarSort, combTerm;
      for(i = 0; i < leftArgs.size(); i++){
        boundVarSort = AH::getNthArg(lhSort, leftArgs.size() - i);
        SList* boundVarSortList = new SList(boundVarSort);

        Literal* newLit = EqHelper::replace(lit, leftArgs[i], freshVar);
        newLit->setPolarity(!newLit->polarity());
        Term* eqForm = Term::createFormula(new Kernel::AtomicFormula(newLit));
        Term* lambdaTerm = Term::createLambda(TermList(eqForm), boundVar, boundVarSortList, AtomicSort::boolSort());
        combTerm = LambdaElimination().elimLambda(lambdaTerm);
        if(!_insertedInstantiations.contains(combTerm)){
        /*cout << "lhs is " + lit->nthArgument(0)->toString() << endl;
        cout << "arg " + leftArgs[i].toString() << endl;
        cout << "inserting " + lambdaTerm->toString() << endl;
        cout << "inserting " + combTerm.toString() << endl;
          _insertedInstantiations.insert(combTerm);
          insertInstantiation(lambdaTerm->getSpecialData()->getSort(), combTerm);
        }
        //may be harmful performance wise, but otherwise these
        //leak
        //eqForm->destroy();
        //lambdaTerm->destroy();

        newLit = EqHelper::replace(lit, rightArgs[i], freshVar);
        newLit->setPolarity(!newLit->polarity());
        eqForm = Term::createFormula(new Kernel::AtomicFormula(newLit));
        lambdaTerm = Term::createLambda(TermList(eqForm), boundVar, boundVarSortList, AtomicSort::boolSort());
        combTerm = LambdaElimination().elimLambda(lambdaTerm);
        if(!_insertedInstantiations.contains(combTerm)){
        /*cout << "rhs is " + lit->nthArgument(1)->toString() << endl;
        cout << "arg " + rightArgs[i].toString() << endl;
        cout << "inserting " + lambdaTerm->toString() << endl;
        cout << "inserting " + combTerm.toString() << endl; 
          _insertedInstantiations.insert(combTerm);
          insertInstantiation(lambdaTerm->getSpecialData()->getSort(), combTerm);
        }

        //eqForm->destroy();
        //lambdaTerm->destroy();

        SList::destroy(boundVarSortList);
      }
    }
  }

  VList::destroy(boundVar);
}*/


} // namespace Indexing
