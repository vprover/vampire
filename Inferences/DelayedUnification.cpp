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
 * @file DelayedUnification.cpp
 * Things for Ahmed/Joe's delayed-unification CADE '23 calculus
 */

#define DEBUG_INSERT(lvl, ...)  if (lvl <= 1) DBG(__VA_ARGS__)
#define DEBUG_PERFORM(lvl, ...) if (lvl <= 0) DBG(__VA_ARGS__)
// increase nr to increase debug verbosity ^

#define CHECK_SIDE_CONDITION(cond, ...)                                                             \
  if(!(cond)) {                                                                                     \
    DEBUG_PERFORM(1, "sidecondition failed: ", __VA_ARGS__)                                         \
    return nullptr;                                                                                 \
  }                                                                                                 \

#include "DelayedUnification.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/SortHelper.hpp"
#include "Indexing/IndexManager.hpp"
#include "Lib/Metaiterators.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/TermIterators.hpp"

namespace Inferences {

void DelayedSubterms::handleClause(Clause *c, bool adding) {
  CALL("DelayedSubterms::handleClause")
  DEBUG_INSERT(1, (adding ? "inserting" : "removing"), ": ", *c)

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator subterms(EqHelper::getSubtermIterator(lit, _ordering));
    while (subterms.hasNext()) {
      TermList t = subterms.next();
      DEBUG_INSERT(1, (adding ? "inserting" : "removing"), ": ", t)

      if(adding){
        _is->insert(t, lit, c);
      } else {
        _is->remove(t, lit, c);
      }
    }
  }
}

void DelayedLHS::handleClause(Clause *c, bool adding) {
  CALL("DelayedLHS::handleClause")
  DEBUG_INSERT(1, (adding ? "inserting" : "removing"), ": ", *c)

  for(unsigned i = 0; i < c->numSelected(); i++) {
    Literal *lit = (*c)[i];
    TermIterator lhs(EqHelper::getSuperpositionLHSIterator(lit, _ordering, _options));
    while (lhs.hasNext()) {
      TermList t = lhs.next();
      DEBUG_INSERT(1, (adding ? "inserting" : "removing"), ": ", t)

      if(adding){
        if(t.isTerm())
          _is->insert(t, lit, c);
        else 
          _variables.insert({c, lit, t});
      } else {
        if(t.isTerm())
          _is->remove(t, lit, c);
        else 
          _variables.remove({c, lit, t});        
      }
    }
  }
}

void DelayedNonEquations::handleClause(Clause *c, bool adding) {
  CALL("DelayedNonEquations::handleClause")
  DEBUG_INSERT(1, (adding ? "inserting" : "removing"), ": ", *c)
  for(unsigned i = 0; i < c->numSelected(); i++){
    Literal* lit = (*c)[i];
    if(!lit->isEquality()){
      handleLiteral(lit, c, adding);
    }
  }
}

void DelayedSuperposition::attach(SaturationAlgorithm *salg) {
  CALL("DelayedSuperposition::attach")
  DelayedInference::attach(salg);
  _subtermIndex = static_cast<DelayedSubterms *>(salg->getIndexManager()->request(DELAYED_SUBTERMS));
  _lhsIndex = static_cast<DelayedLHS *>(salg->getIndexManager()->request(DELAYED_EQUATIONS));
  ASS_EQ(_ord , &salg->getOrdering())
  ASS_EQ(_opts, &salg->getOptions())
}

Clause *DelayedSuperposition::perform(
  Clause *equationClause,
  Literal *equation,
  TermList lhs,
  Clause *subtermClause,
  Literal *subtermLiteral,
  Term *subterm
) {
  CALL("DelayedSuperposition::perform")
  DEBUG_PERFORM(1, "lhs: ", *equationClause, " [ ", *equation      , " ][ ", lhs     , " ]")
  DEBUG_PERFORM(1, "rhs: ", *subtermClause , " [ ", *subtermLiteral, " ][ ", *subterm, " ]")

  // prevent self-superposition l = r in l = r to get r = r, which seems to happen a surprising amount
  if(equationClause == subtermClause && equation == subtermLiteral && TermList(subterm) == lhs)
    return nullptr;

  // TODO if lhs is a var, check that the rewrite is well-sorted
  // TODO if lhs is a var, call checkSuperpositionFromVariable?

  TermList rhs = EqHelper::getOtherEqualitySide(equation, lhs);

  // compute a renaming for both clauses so that variables are disjoint
  Renaming equationRenaming;
  for(unsigned i = 0; i < equationClause->length(); i++)
    equationRenaming.normalizeVariables((*equationClause)[i]);

  Renaming subtermRenaming(equationClause->varCnt());
  for(unsigned i = 0; i < subtermClause->length(); i++)
    subtermRenaming.normalizeVariables((*subtermClause)[i]);

  // some helpfully-renamed terms
  TermList lhs_renamed = equationRenaming.apply(lhs);
  TermList rhs_renamed = equationRenaming.apply(rhs);
  Term *subterm_renamed = subtermRenaming.apply(subterm);

  // if lhs is a var, check subterm > rhs
  if(lhs.isVar() && Ordering::isGorGEorE(_ord->compare(rhs_renamed, TermList(subterm_renamed))))
    return nullptr;

  // check that the lhs and the target might unify, one day
  if(!mightPossiblyUnify(lhs_renamed, TermList(subterm_renamed)))
    return nullptr;

  // TODO check whether we are rewriting smaller side of equation? superposition checks this here

  // the rewritten literal
  Literal *rewritten = EqHelper::replace(
    subtermRenaming.apply(subtermLiteral),
    TermList(subterm_renamed),
    equationRenaming.apply(rhs)
  );
  if(EqHelper::isEqTautology(rewritten))
    return nullptr;

  // compute clause length and create a blank clause to fill
  unsigned arity = lhs.isVar() ? 0 : lhs.term()->arity();
  unsigned length = equationClause->length() + subtermClause->length() + arity - 1;
  Inference inference(GeneratingInference2(
    InferenceRule::DELAYED_SUPERPOSITION,
    equationClause,
    subtermClause
  ));
  Clause *cl = new (length) Clause(length, inference);

  // how far are we through the clause?
  unsigned i = 0;

  // copy side literals into new clause from old, applying the renaming
  for(unsigned j = 0; j < equationClause->length(); j++)
    if((*equationClause)[j] != equation)
      (*cl)[i++] = equationRenaming.apply((*equationClause)[j]);
  for(unsigned j = 0; j < subtermClause->length(); j++)
    if((*subtermClause)[j] != subtermLiteral)
      (*cl)[i++] = subtermRenaming.apply((*subtermClause)[j]);

  // add rewritten literal
  (*cl)[i++] = rewritten;

  if(lhs.isTerm()) {
    Term *lhs_renamed_term = lhs_renamed.term();
    ASS_EQ(lhs_renamed_term->functor(), subterm_renamed->functor())

    // create disequations
    for(unsigned j = 0; j < arity; j++) {
      TermList larg = (*lhs_renamed_term)[j];
      TermList rarg = (*subterm_renamed)[j];
      // TODO deal with polymorphic sorts properly: this will work until it doesn't
      TermList sort = SortHelper::getArgSort(subterm_renamed, j);
      Literal *disequation = Literal::createEquality(false, larg, rarg, sort);
      (*cl)[i++] = disequation;
    }
  }
  else {
    ASS(lhs_renamed.isVar())

    // apply substitution of lhs -> subterm
    // OK to do this as a naive replacement because of single binding with disjoint variables
    for(unsigned i = 0; i < cl->length(); i++)
      (*cl)[i] = EqHelper::replace(
        (*cl)[i],
        lhs_renamed,
        TermList(subterm_renamed)
      );

    // TODO check literals are still maximal under substitution?
  }

  /*
  std::cout << equationClause->toString() << std::endl;
  std::cout << lhs.toString() << " -> " << rhs.toString() << std::endl;
  std::cout << subtermClause->toString() << std::endl;
  std::cout << subtermLiteral->toString() << std::endl;
  std::cout << subterm->toString() << std::endl;
  std::cout << cl->toString() << std::endl;
  std::cout << "-----------------------------" << std::endl;
  */
  return cl;
}

ClauseIterator DelayedSuperposition::generateClauses(Clause *cl) {
  CALL("DelayedSuperposition::generateClauses")

  typedef TopSymbolIndex<Term *>::Entry TEntry;
  typedef TopSymbolIndex<TermList>::Entry TLEntry;
  typedef std::pair<TLEntry, TEntry> Superposition;

  // selected literals
  auto fwselected = cl->getSelectedLiteralIterator();

  // rewritable subterms of selected literals
  auto fwsubterms = getMapAndFlattenIterator(fwselected, [this, cl](Literal *lit) {
    // TODO avoid boxing here? should not be necessary, but there are some move-semantic errors
    return pvi(getMappingIterator(
      EqHelper::getSubtermIterator(lit, *_ord),
      [lit, cl](TermList term) -> TEntry { return { cl, lit, term.term() }; }
    ));
  });

  // forward superpositions
  auto fwsuperpositions = getMapAndFlattenIterator(fwsubterms, [this](TEntry subterm) {
    return pvi(getMappingIterator(
      getConcatenatedIterator(
        getMappingIterator(
          _lhsIndex->getUnifications(TermList(subterm.term), false),
          [](TermQueryResult tqr) -> TLEntry {
            return { tqr.clause, tqr.literal, tqr.term }; 
          }
        ),
        _lhsIndex->variables()
      ),
      [subterm](TLEntry rewrite) -> Superposition { return { rewrite, subterm }; }
    ));
  });

  // selected literals
  auto bwselected = cl->getSelectedLiteralIterator();

  // oriented equations in selected literals
  auto bwrewrites = getMapAndFlattenIterator(bwselected, [this, cl](Literal *lit) {
    return pvi(getMappingIterator(
      EqHelper::getSuperpositionLHSIterator(lit, *_ord, *_opts),
      [cl, lit](TermList lhs) -> TLEntry { return { cl, lit, lhs }; }
    ));
  });

  // backward superpositions
  auto bwsuperpositions = getMapAndFlattenIterator(bwrewrites, [this](TLEntry rewrite) {
    return pvi(getMappingIterator(
      _subtermIndex->getUnifications(rewrite.term, false),
      [rewrite](TermQueryResult tqr) -> Superposition { return { rewrite, { tqr.clause, tqr.literal, tqr.term.term() } }; }
    ));
  });

  // fw + bw superpositions
  auto superpositions = getConcatenatedIterator(fwsuperpositions, bwsuperpositions);

  // all resulting superposition attempts
  auto attempts = getMappingIterator(superpositions, [this](Superposition superposition) {
    TLEntry rewrite = superposition.first;
    TEntry subterm = superposition.second;
    return perform(
      rewrite.clause,
      rewrite.literal,
      rewrite.term,
      subterm.clause,
      subterm.literal,
      subterm.term
    );
  });

  return pvi(getFilteredIterator(attempts, [](Clause *c) { return c; }));
}

void DelayedBinaryResolution::attach(SaturationAlgorithm *salg) {
  CALL("DelayedBinaryResolution::attach")
  DelayedInference::attach(salg);
  _index = static_cast<DelayedNonEquations *>(salg->getIndexManager()->request(DELAYED_NONEQUATIONS));
}

Clause *DelayedBinaryResolution::perform(
  Clause *leftClause,
  Literal *leftLit,
  Clause *rightClause,
  Literal *rightLit
) {
  CALL("DelayedBinaryResolution::perform")
  ASS_EQ(leftLit->functor(), rightLit->functor())
  ASS_NEQ(leftLit->polarity(), rightLit->polarity())
  ASS(!leftLit->isEquality())
  DEBUG_PERFORM(1, "lhs: ", *leftClause, " [ ", *leftLit     , " ]")
  DEBUG_PERFORM(1, "rhs: ", *rightClause, " [ ", *rightLit     , " ]")

  // compute a renaming for both clauses so that variables are disjoint
  Renaming leftRenaming;
  for(unsigned i = 0; i < leftClause->length(); i++)
    leftRenaming.normalizeVariables((*leftClause)[i]);
  Renaming rightRenaming(leftClause->varCnt());
  for(unsigned i = 0; i < rightClause->length(); i++)
    rightRenaming.normalizeVariables((*rightClause)[i]);

  // some helpfully-renamed terms
  Literal *leftLitRenamed = leftRenaming.apply(leftLit);
  Literal *rightLitRenamed = rightRenaming.apply(rightLit);

  // check that the lhs and the target might unify, one day
  if(!mightPossiblyUnify(TermList(leftLitRenamed), TermList(rightLitRenamed)))
    return nullptr;

  // compute clause length and create a blank clause to fill
  unsigned arity = leftLit->arity();
  unsigned length = leftClause->length() + rightClause->length() + arity - 2;
  Inference inference(GeneratingInference2(
    InferenceRule::DELAYED_BINARY_RESOLUTION,
    leftClause,
    rightClause
  ));
  Clause *cl = new (length) Clause(length, inference);

  // how far are we through the clause?
  unsigned i = 0;

  // copy side literals into new clause from old, applying the renaming
  for(unsigned j = 0; j < leftClause->length(); j++)
    if((*leftClause)[j] != leftLit)
      (*cl)[i++] = leftRenaming.apply((*leftClause)[j]);
  for(unsigned j = 0; j < rightClause->length(); j++)
    if((*rightClause)[j] != rightLit)
      (*cl)[i++] = rightRenaming.apply((*rightClause)[j]);

  //create disequations
  for(unsigned j = 0; j < arity; j++) {
    TermList larg = (*leftLitRenamed)[j];
    TermList rarg = (*rightLitRenamed)[j];
    // TODO deal with polymorphic sorts properly: this will work until it doesn't
    TermList sort = SortHelper::getArgSort(leftLitRenamed, j);
    Literal *disequation = Literal::createEquality(false, larg, rarg, sort);
    (*cl)[i++] = disequation;
  }

  return cl;
}



ClauseIterator DelayedBinaryResolution::generateClauses(Clause *cl) {
  CALL("DelayedBinaryResolution::generateClauses")

  auto selected = cl->getSelectedLiteralIterator();
  auto resolutions = getMapAndFlattenIterator(selected, [this, cl](Literal *lit) {
    return getMappingIterator(
      // true means get complementary literals that could unify
      _index->getUnifications(lit,true),
      [this, cl, lit](SLQueryResult res) {
        return perform(
          res.clause,
          res.literal,
          cl,
          lit
        );
      }
    );
  });
  return pvi(getFilteredIterator(resolutions, [](Clause *c) { return c; }));
}

struct DelayedBind {
  TermList var;
  TermList bound;

  friend std::ostream& operator<<(std::ostream& out, DelayedBind const& self)
  { return out  << "Bind(" << self.var << " -> " << self.bound << ")"; }
};

struct DelayedDecompose {
  Term* t1;
  Term* t2;

  friend std::ostream& operator<<(std::ostream& out, DelayedDecompose const& self)
  { return out  << "Decompose(" << *self.t1 << ", " << *self.t2 << ")"; }
};
struct DelayedRefl 
{ friend std::ostream& operator<<(std::ostream& out, DelayedRefl const& self) { return out << "Refl"; } };

struct DelayedUnifier 
: public Coproduct<DelayedBind, DelayedDecompose, DelayedRefl> 
{ 
  template<class C> 
  DelayedUnifier(C c) : Coproduct<DelayedBind, DelayedDecompose, DelayedRefl>(std::move(c)) {}

  template<class T>
  T sigma(T t) 
  { return match(
        [&](DelayedBind&    b) { return b.var == b.bound ? t : EqHelper::replace(t, b.var, b.bound); },
        [&](DelayedDecompose&) { return t; },
        [&](DelayedRefl&) { return t; }
        ); }
  template<class F>
  auto forConstraints(F action)
  { return match(
        [&](DelayedBind&) { /* no constraints */ },
        [&](DelayedDecompose& d) { 
          ASS_EQ(d.t1->functor(), d.t2->functor());
          ASS_EQ(d.t1->numTypeArguments(), 0) // <- polymorphism not suppoted yet
          for (auto tup : termArgIter(d.t1).zip(termArgIter(d.t2)).zipWithIndex()) {
            auto sort = SortHelper::getArgSort(d.t1, tup.second);
            action(Literal::createEquality(false, tup.first.first, tup.first.second, sort));
          }
        },
        [&](DelayedRefl& d) { /* no constraints */ }
        ); }
};

Option<DelayedUnifier> unifDelayed(Literal* t1, Literal* t2)
{
  if (t1 == t2) {
    return some(DelayedUnifier(DelayedRefl {} ));

  } else if (t1->functor() == t2->functor() 
         && t1->polarity() == t2->polarity() ) {
    return some(DelayedUnifier(DelayedDecompose { .t1 = t1, .t2 = t2, }));

  } else {
    return {};
  }
}
Option<DelayedUnifier> unifDelayed(TermList t1, TermList t2)
{
  auto strictSubterm = [](TermList v, TermList t) 
  { return v != t && t.containsSubterm(v); };

  if (t1 == t2) {
    return some(DelayedUnifier(DelayedRefl {} ));

  } else if (t1.isVar() && !strictSubterm(t1, t2)) {
    return some(DelayedUnifier(DelayedBind { .var = t1, .bound = t2 }));

  } else if (t2.isVar() && !strictSubterm(t2, t1)) {
    return some(DelayedUnifier(DelayedBind { .var = t2, .bound = t1 }));

  } else if (t1.isTerm() && t2.isTerm() 
      && t1.term()->functor() == t2.term()->functor()) {
    return some(DelayedUnifier(DelayedDecompose { .t1 = t1.term(), .t2 = t2.term() }));

  } else {
    return {};
  }
}

//  C \/ L1 \/ L2
// =========================
// (C \/ L1 \/ L2) unif
//
// where
// - L1, and L2 are selected
// - unif = delayedUnification(l1, l2)
Clause* DelayedFactoring::perform(Clause* cl
    , unsigned i1 // <- index of L1
    , unsigned i2 // <- index of L2
    ) const 
{
  CALL("DelayedFactoring::perform")
  auto lit1 = (*cl)[i1];
  auto lit2 = (*cl)[i2];
  // check whther L1 and L2 are unifiable, and positive
  if (lit1->isNegative() || lit2->isNegative() || lit1->functor() != lit2->functor())
    return nullptr;

  DEBUG_PERFORM(1, *lit1, " | ", *lit2, " | rest");

  auto unif = unifDelayed(lit1, lit2);
  DEBUG_PERFORM(2, "unifier: ", unif)
  ASS(unif.isSome());
  ASS(unif->is<DelayedDecompose>() || unif->is<DelayedRefl>());

  Stack<Literal*> conclusion;

  // L1 or L2 to the conclusion. if either is ground we keep that one
  conclusion.push(unif->sigma(unif->sigma(lit2)->ground() ? lit2 : lit1));
  // add all the constraints
  unif->forConstraints([&](auto c) { conclusion.push(c); });
  // add all other literals from the hypothesis
  conclusion.loadFromIterator(
      range(0,cl->size())
        .filter([&](auto i) { return i != i1 && i != i2; })
        .map([&](auto i) { return unif->sigma((*cl)[i]); })
      );

  auto out = Clause::fromStack(
      conclusion,
      Inference(GeneratingInference1(
        InferenceRule::DELAYED_FACTORING,
        cl
      )));
  DEBUG_PERFORM(1, "result: ", *out);
  return out;
}

void DelayedFactoring::attach(SaturationAlgorithm *salg) {
  CALL("DelayedFactoring::attach")
  GeneratingInferenceEngine::attach(salg);
  ASS_EQ(_ord , &salg->getOrdering())
  ASS_EQ(_opts, &salg->getOptions())
}


// C \/ l1 == r1 \/ l2 == r2
// =========================
// (C \/ r1 != r2 \/ l2 == r2) unif
//
// where
// - l2 == r2 is selected
// - !(l2 <= r2)
// - unif = delayedUnification(l1, l2)
Clause* DelayedEqualityFactoring::perform(Clause* cl
    , unsigned lit1 // <- index of l1 == r1
    , unsigned term1// <- index of l1 in l1 == r1
    , unsigned lit2 // <- index of l2 == r2
    , unsigned term2 // <- index of l2 in l2 == r2
    ) const 
{
  CALL("DelayedEqualityFactoring::perform")
  auto sort1 = SortHelper::getEqualityArgumentSort((*cl)[lit1]);
  auto sort2 = SortHelper::getEqualityArgumentSort((*cl)[lit2]);
  auto l1 = *(*cl)[lit1]->nthArgument(term1);
  auto r1 = *(*cl)[lit1]->nthArgument(1 - term1);
  auto l2 = *(*cl)[lit2]->nthArgument(term2);
  auto r2 = *(*cl)[lit2]->nthArgument(1 - term2);
  DEBUG_PERFORM(1, l1, " == ", r1, " | ", l2, " == ", r2, " | rest");

  auto notLeq = [](Ordering::Result r) {
    switch (r) {
      case Ordering::Result::GREATER: return true;
      case Ordering::Result::INCOMPARABLE: return true;
      case Ordering::Result::GREATER_EQ: ASSERTION_VIOLATION_REP("TODO");
      case Ordering::Result::EQUAL: return false;
      case Ordering::Result::LESS_EQ: return false;
      case Ordering::Result::LESS: return false;
      default: ASSERTION_VIOLATION
    }
  };

  CHECK_SIDE_CONDITION(sort2 == sort1, "sort1 == sort2. sort1 :", sort1, "\tsort2: ", sort2)
  auto sort = sort1;
  CHECK_SIDE_CONDITION(notLeq(_ord->compare(l2, r2)), "not(l2 <= r2). l2 :", l2, "\tr2: ", r2)
  CHECK_SIDE_CONDITION(notLeq(_ord->compare(l1, r1)), "not(l1 <= r1). l1 :", l1, "\tr1: ", r1)

  auto unif = unifDelayed(l1, l2);
  DEBUG_PERFORM(2, "unifier: ", unif)
  CHECK_SIDE_CONDITION(unif.isSome(), "unifiable(l1, l2). l1 :", l1, "\tl2: ", l2)


  Stack<Literal*> conclusion;
  conclusion.push(Literal::createEquality(false, unif->sigma(r1), unif->sigma(r2), sort));
  // r1 != r2 <---^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  conclusion.push(Literal::createEquality(true, unif->sigma(l2), unif->sigma(r2), sort));
  // l2 == r2 <---^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  unif->forConstraints([&](auto c) { conclusion.push(c); });

  conclusion.loadFromIterator(
      range(0,cl->size())
        .filter([&](auto i) { return i != lit1 && i != lit2; })
        .map([&](auto i) { return unif->sigma((*cl)[i]); })
      );


  auto out = Clause::fromStack(
      conclusion,
      Inference(GeneratingInference1(
        InferenceRule::DELAYED_EQUALITY_FACTORING,
        cl
      )));
  DEBUG_PERFORM(1, "result: ", *out);
  return out;
}
ClauseIterator DelayedEqualityFactoring::generateClauses(Clause *cl) {
  CALL("DelayedEqualityFactoring::generateClauses")
  return pvi(
      cl->selectedIndices()
        .flatMap([cl](auto selIdx) {
            return pvi(range(0, cl->size())
                .filter([=](auto j){ return j != selIdx; })
                .map([=](auto j) { return make_pair(j, selIdx); }));
        })
        .filter([cl](auto pair) { 
            auto posEquality = [](auto l) { return l->isPositive() && l->isEquality(); };
            return posEquality((*cl)[pair.first]) && posEquality((*cl)[pair.second]); 
        })
        .flatMap([=](auto pair) {
            return range(0u,2u) // <- iterator over equality side indices
              .flatMap([=](auto term1) {
                  return range(0u, 2u)  // <- iterator over equality side indices
                    .map([=](auto term2) {
                        return perform(cl, pair.first, term1, pair.second, term2);
                    })
                    .filter([](auto x) { return x != nullptr; });
              });
        })
    );
}


void DelayedEqualityFactoring::attach(SaturationAlgorithm *salg) {
  CALL("DelayedEqualityFactoring::attach")
  GeneratingInferenceEngine::attach(salg);
  ASS_EQ(_ord , &salg->getOrdering())
  ASS_EQ(_opts, &salg->getOptions())
}

ClauseIterator DelayedFactoring::generateClauses(Clause *cl) {
  CALL("DelayedFactoring::generateClauses")
  return pvi(
      range(0, cl->numSelected())
        .flatMap([this, cl](auto i) {
            return pvi(range(i + 1, cl->size())
                .map([this, i, cl](auto j) { 
                  return perform(cl, i, j); })
                .filter([](auto x) { return x != nullptr; }));
            ;
        })
    );
}


void DelayedEqualityResolution::attach(SaturationAlgorithm *salg) {
  CALL("DelayedEqualityResolution::attach")
  GeneratingInferenceEngine::attach(salg);
  ASS_EQ(_ord , &salg->getOrdering())
  ASS_EQ(_opts, &salg->getOptions())
}

ClauseIterator DelayedEqualityResolution::generateClauses(Clause *cl) {
  CALL("DelayedEqualityResolution::generateClauses")
  return pvi(
      cl->selectedIndices()
        .filter([=](auto i) { return (*cl)[i]->isEquality() && (*cl)[i]->isNegative(); })
        .map([=](auto i) 
          { return perform(cl, i); })
        .filter([](auto x) { return x != nullptr; })
    );
}

Clause* DelayedEqualityResolution::perform(Clause* cl, unsigned idx) const {
  CALL("DelayedEqualityResolution::perform")
  auto lit = (*cl)[idx];
  auto l = *lit->nthArgument(0);
  auto r = *lit->nthArgument(1);

  DEBUG_PERFORM(1, l, " != ", r, " | rest");

  auto unif = unifDelayed(l, r);
  DEBUG_PERFORM(2, "unifier: ", unif)
  CHECK_SIDE_CONDITION(unif.isSome(), "unifiable(l, r). l :", l, "\tr: ", r)

  Stack<Literal*> conclusion;
  unif->forConstraints([&](auto c) { conclusion.push(c); });

  conclusion.loadFromIterator(
      range(0,cl->size())
        .filter([&](auto i) { return i != idx; })
        .map([&](auto i) { return unif->sigma((*cl)[i]); })
      );

  auto out = Clause::fromStack(
      conclusion, 
      Inference(GeneratingInference1(
        InferenceRule::DELAYED_EQUALITY_RESOLUTION,
        cl
      )));

  DEBUG_PERFORM(1, "result: ", *out);
  return out;

}

} //namespace Inferences
