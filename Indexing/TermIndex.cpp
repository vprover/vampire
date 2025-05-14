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

#include "Forwards.hpp"
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

#include "Shell/LambdaElimination.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

#include "TermIndex.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto rsti = env.options->combinatorySup() ? EqHelper::getFoSubtermIterator(lit,_ord)
                                              : EqHelper::getSubtermIterator(lit,_ord);
    while (rsti.hasNext()) {
      auto tt = TypedTermList(rsti.next());
      ((TermSubstitutionTree<TermLiteralClause>*)&*_is)->handle(TermLiteralClause{ tt, lit, c }, adding);
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("forward superposition index maintenance");

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto lhsi = EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
	    _tree->handle(TermLiteralClause{ lhsi.next(), lit, c }, adding);
    }
  }
}

template <bool combinatorySupSupport>
void DemodulationSubtermIndexImpl<combinatorySupSupport>::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("backward demodulation index maintenance");

  static DHSet<Term*> inserted;

  bool skipNonequationalLiterals = _opt.demodulationOnlyEquational();

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    // it is true (as stated below) that inserting only once per clause would be sufficient
    // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
    // so if the order changes while a clause is in the index (which can happen with "-sa otter")
    // the removes could be called on different literals than the inserts!
    inserted.reset();
    Literal* lit=(*c)[i];
    if (lit->isAnswerLiteral()) {
      continue;
    }
    if (skipNonequationalLiterals && !lit->isEquality()) {
      continue;
    }
    typename std::conditional<!combinatorySupSupport,
      NonVariableNonTypeIterator,
      FirstOrderSubtermIt>::type it(lit);
    while (it.hasNext()) {
      Term* t= it.next();
      if (!inserted.insert(t)) {//TODO existing error? Terms are inserted once per a literal
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        it.right();
        continue;
      }
      if (adding) {
        _is->insert(TermLiteralClause{ t, lit, c });
      } else {
        _is->remove(TermLiteralClause{ t, lit, c });
      }
    }
  }
}

// This is necessary for templates defined in cpp files.
// We are happy to do it for DemodulationSubtermIndexImpl, since it (at the moment) has only two specializations:
template class DemodulationSubtermIndexImpl<false>;
template class DemodulationSubtermIndexImpl<true>;

void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  if (c->length()!=1) {
    return;
  }

  TIME_TRACE("forward demodulation index maintenance");

  Literal* lit=(*c)[0];
  auto [lhsi, preordered] = EqHelper::getDemodulationLHSIterator(
      lit, _opt.forwardDemodulation()== Options::Demodulation::PREORDERED, _ord);

  while (lhsi.hasNext()) {
    auto lhs = lhsi.next();

    // DemodulatorData expects lhs and rhs to be normalized
    Renaming r;
    r.normalizeVariables(lhs);

    DemodulatorData dd(
      TypedTermList(r.apply(lhs),r.apply(lhs.sort())),
      r.apply(EqHelper::getOtherEqualitySide(lit, lhs)),
      c, preordered, _ord
    );
    _is->handle(std::move(dd), adding);
  }
}

void InductionTermIndex::handleClause(Clause* c, bool adding)
{
  TIME_TRACE("induction term index maintenance");

  if (!InductionHelper::isInductionClause(c)) {
    return;
  }

  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    Literal* lit = (*c)[i];
    if (!InductionHelper::isGroundInductionLiteral(lit)) {
      continue;
    }

    DHSet<Term*> done;
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      Term* t = it.next();
      if (!done.insert(t)) {
        it.right();
        continue;
      }
      if (t->isLiteral()) {
        continue;
      }
      if (InductionHelper::isInductionTermFunctor(t->functor()) &&
          InductionHelper::isIntInductionTermListInLiteral(t, lit)) {
        if (adding) {
          _is->insert(TermLiteralClause{ t, lit, c });
        } else {
          _is->remove(TermLiteralClause{ t, lit, c });
        }
      }
    }
  }
}

void StructInductionTermIndex::handleClause(Clause* c, bool adding)
{
  if (!InductionHelper::isInductionClause(c)) {
    return;
  }
  static DHSet<Term*> inserted;
  // Iterate through literals & check if the literal is suitable for induction
  for (unsigned i=0;i<c->length();i++) {
    inserted.reset();
    Literal* lit = (*c)[i];
    if (!lit->ground()) {
      continue;
    }
    NonVariableNonTypeIterator it(lit);
    while (it.hasNext()) {
      Term* t = it.next();
      if (!inserted.insert(t)) {
        it.right();
        continue;
      }
      if (t->isLiteral()) {
        continue;
      }
      if (InductionHelper::isInductionTermFunctor(t->functor()) &&
          InductionHelper::isStructInductionTerm(t)) {
        if (adding) {
          _is->insert(TermLiteralClause{ t, lit, c });
        } else {
          _is->remove(TermLiteralClause{ t, lit, c });
        }
      }
    }
  }
}


/////////////////////////////////////////////////////
// Indices for higher-order inferences from here on//
/////////////////////////////////////////////////////

void SubVarSupSubtermIndex::handleClause(Clause* c, bool adding)
{
  DHSet<unsigned> unstableVars;
  c->collectUnstableVars(unstableVars);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto rvi = EqHelper::getRewritableVarsIterator(&unstableVars, lit,_ord);
    while(rvi.hasNext()){
      _is->handle(TermLiteralClause{ rvi.next(), lit, c }, adding);
    }
  }
}

void SubVarSupLHSIndex::handleClause(Clause* c, bool adding)
{
  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    auto lhsi = EqHelper::getSubVarSupLHSIterator(lit, _ord);
    while (lhsi.hasNext()) {
      _is->handle(TermLiteralClause{ lhsi.next(), lit, c }, adding);
    }
  }
}
void PrimitiveInstantiationIndex::populateIndex()
{
  typedef ApplicativeHelper AH;

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
    _is->insert(TermWithoutValue(kTerm1.term()));
    _is->insert(TermWithoutValue(kTerm2.term()));
    _is->insert(TermWithoutValue(andTerm.term()));
    _is->insert(TermWithoutValue(orTerm.term()));
    _is->insert(TermWithoutValue(impTerm.term()));
    _is->insert(TermWithoutValue(notTerm.term()));
    _is->insert(TermWithoutValue(equalsTerm.term()));
    _is->insert(TermWithoutValue(notEqualsTerm.term()));
  } else if (set == Options::PISet::ALL_EXCEPT_NOT_EQ){
    _is->insert(TermWithoutValue(kTerm1.term()));
    _is->insert(TermWithoutValue(kTerm2.term()));
    _is->insert(TermWithoutValue(andTerm.term()));
    _is->insert(TermWithoutValue(orTerm.term()));
    _is->insert(TermWithoutValue(impTerm.term()));
    _is->insert(TermWithoutValue(notTerm.term()));
    _is->insert(TermWithoutValue(equalsTerm.term()));
  } else if (set == Options::PISet::FALSE_TRUE_NOT){
    _is->insert(TermWithoutValue(kTerm1.term()));
    _is->insert(TermWithoutValue(kTerm2.term()));
    _is->insert(TermWithoutValue(notTerm.term()));
  } else if (set == Options::PISet::FALSE_TRUE_NOT_EQ_NOT_EQ){
    _is->insert(TermWithoutValue(kTerm1.term()));
    _is->insert(TermWithoutValue(kTerm2.term()));
    _is->insert(TermWithoutValue(notTerm.term()));
    _is->insert(TermWithoutValue(equalsTerm.term()));
    _is->insert(TermWithoutValue(notEqualsTerm.term()));
  }
}

void NarrowingIndex::populateIndex()
{
  typedef ApplicativeHelper AH;

  static Options::Narrow set = env.options->narrow();

  auto srtOf = [] (TermList t) {
     ASS(t.isTerm());
     return SortHelper::getResultSort(t.term());
  };

  TermList s1 = TermList(0, false);
  TermList s2 = TermList(1, false);
  TermList s3 = TermList(2, false);
  TermList x = TermList(3, false);
  TermList y = TermList(4, false);
  TermList z = TermList(5, false);
  TermList args[] = {s1, s2, s3};

  unsigned s_comb = env.signature->getCombinator(Signature::S_COMB);
  TermList constant = TermList(Term::create(s_comb, 3, args));
  TermList lhsS = AH::createAppTerm(srtOf(constant), constant, x, y, z);
  TermList rhsS = AH::createAppTerm3(AtomicSort::arrowSort(s1, s2, s3), x, z, AH::createAppTerm(AtomicSort::arrowSort(s1, s2), y, z));
  Literal* sLit = Literal::createEquality(true, lhsS, rhsS, s3);

  unsigned c_comb = env.signature->getCombinator(Signature::C_COMB);
  constant = TermList(Term::create(c_comb, 3, args));  TermList lhsC = AH::createAppTerm(srtOf(constant), constant, x, y, z); 
  TermList rhsC = AH::createAppTerm3(AtomicSort::arrowSort(s1, s2, s3), x, z, y);
  Literal* cLit = Literal::createEquality(true, lhsC, rhsC, s3);

  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  constant = TermList(Term::create(b_comb, 3, args));
  TermList lhsB = AH::createAppTerm(srtOf(constant), constant, x, y, z); 
  TermList rhsB = AH::createAppTerm(AtomicSort::arrowSort(s2, s3), x, AH::createAppTerm(AtomicSort::arrowSort(s1, s2), y, z));
  Literal* bLit = Literal::createEquality(true, lhsB, rhsB, s3);

  unsigned k_comb = env.signature->getCombinator(Signature::K_COMB);
  constant = TermList(Term::create2(k_comb, s1, s2));
  TermList lhsK = AH::createAppTerm3(srtOf(constant), constant, x, y);
  Literal* kLit = Literal::createEquality(true, lhsK, x, s1);

  unsigned i_comb = env.signature->getCombinator(Signature::I_COMB);
  constant = TermList(Term::create1(i_comb, s1));
  TermList lhsI = AH::createAppTerm(srtOf(constant), constant, x);
  Literal* iLit = Literal::createEquality(true, lhsI, x, s1);

  if(set == Options::Narrow::ALL){
    _is->insert(TermWithValue<Literal*>(lhsS.term(), sLit));
    _is->insert(TermWithValue<Literal*>(lhsC.term(), cLit));
    _is->insert(TermWithValue<Literal*>(lhsB.term(), bLit));
    _is->insert(TermWithValue<Literal*>(lhsK.term(), kLit));
    _is->insert(TermWithValue<Literal*>(lhsI.term(), iLit));
  } else if (set == Options::Narrow::SKI) {
    _is->insert(TermWithValue<Literal*>(lhsS.term(), sLit));
    _is->insert(TermWithValue<Literal*>(lhsK.term(), kLit));
    _is->insert(TermWithValue<Literal*>(lhsI.term(), iLit));
  } else if (set == Options::Narrow::SK){
    _is->insert(TermWithValue<Literal*>(lhsS.term(), sLit));
    _is->insert(TermWithValue<Literal*>(lhsK.term(), kLit));
  }
}

void SkolemisingFormulaIndex::insertFormula(TermList formula, TermList skolem)
{
  _is->insert(TermWithValue<TermList>(TypedTermList(formula.term()), skolem));
}

} // namespace Indexing
