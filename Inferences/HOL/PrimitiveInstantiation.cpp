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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Kernel/HOL/HOL.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "PrimitiveInstantiation.hpp"

namespace Inferences
{
using namespace HOL::create;

struct PrimitiveInstResultFn
{
  using IndexPairStack = Stack<std::pair<unsigned, unsigned>>;

  PrimitiveInstResultFn(Clause* cl, const Options::PISet piSet): _cl(cl), _freshVar(cl->maxVar() + 1), _piSet(piSet)
  {
    auto sortVar = TermList::var(_freshVar++);

    // TODO rather than constantly recreating this stack
    // and pushing on the terms every time we run a prim inst inference
    // another option is to use RobSubstitution and allow it to
    // rename terms apart. That way, we don't need to worry about freshness
    // of variables. The potential downside is that the whole RobSubstitution
    // mechanism is complicated and may add its own overhead. Worth investigating
    // though
    _heads.push(top());
    _heads.push(bottom());
    switch (_piSet) {
      case Options::PISet::ALL_EXCEPT_NOT_EQ:
      case Options::PISet::ALL:
        _heads.push(conj());
        _heads.push(disj());
        _heads.push(neg());
        _heads.push(equality(sortVar));
        _heads.push(pi(sortVar));
        _heads.push(sigma(sortVar));
        break;
      case Options::PISet::PRAGMATIC:
      case Options::PISet::NOT:
        _heads.push(neg());
        break;
      // Equality and Pi and Sigma introduce polymorphism
      // into monomorphic problem...
      case Options::PISet::NOT_EQ_NOT_EQ:
        _heads.push(neg());
        _heads.push(equality(sortVar));
        break;
      case Options::PISet::AND:
        _heads.push(conj());
        break;
      case Options::PISet::OR:
        _heads.push(disj());
        break;
      case Options::PISet::EQUALS:
        _heads.push(equality(sortVar));
        break;
      case Options::PISet::PI_SIGMA:
        _heads.push(pi(sortVar));
        _heads.push(sigma(sortVar));
        break;
    }
  }

  IndexPairStack getSameSortIndices(const TermStack& sorts)
  {
    IndexPairStack res;
    for (unsigned i = 0; i < sorts.size(); i++) {
      for (unsigned j = i + 1; j < sorts.size(); j++) {
        if (sorts[i] == sorts[j]) {
          res.push({ i, j });
        }
      }
    }
    return res;
  }

  ClauseIterator operator() (Literal* lit)
  {
    const bool pragmatic = _piSet == Options::PISet::PRAGMATIC;
    const bool include_not_eq = _piSet == Options::PISet::ALL ||
                                 _piSet == Options::PISet::NOT_EQ_NOT_EQ;

    static ClauseStack results;
    results.reset();

    auto [lhs, rhs] = lit->eqArgs();

    // Flex term is of form X a1 ... an
    TermList flexTerm = lhs.head().isVar() ? lhs : rhs;

    // since term is rigid, cannot be a variable
    TermList headFlex;
    TermStack argsFlex;
    TermStack sortsFlex; //sorts of arguments of flex head

    HOL::getHeadArgsAndArgSorts(flexTerm, headFlex, argsFlex, sortsFlex);
    ASS_EQ(argsFlex.size(), sortsFlex.size());

    if (!argsFlex.size()) {
      // TODO do we really want to do this?
      return ClauseIterator::getEmpty();
    }

    auto pushResult = [this,headFlex](TermList binding)
    {
      static Substitution subst;
      subst.reset();
      subst.bind(headFlex.var(), binding);
      results.push(Clause::fromIterator(
        _cl->iterLits().map([](Literal* lit) { return SubstHelper::apply(lit, subst); }),
        GeneratingInference1(InferenceRule::PRIMITIVE_INSTANTIATION, _cl)));
    };

    // if any amongst a1 ... an is of sort $o, project that argument to the top
    for (unsigned i = 0; i < sortsFlex.size() && pragmatic; i++) {
      if (sortsFlex[i].isBoolSort()) {
        pushResult(surroundWithLambdas(HOL::getDeBruijnIndex(i, sortsFlex[i]), sortsFlex));
      }
    }

    if (pragmatic) {
      for (const auto& [i,j] : getSameSortIndices(sortsFlex)) {
        TermList dbi = HOL::getDeBruijnIndex(i, sortsFlex[i]);
        TermList dbj = HOL::getDeBruijnIndex(j, sortsFlex[j]);

        TermList tm = app(equality(sortsFlex[i]), {dbi, dbj});
        // creating dbi = dbj
        pushResult(surroundWithLambdas(tm, sortsFlex));

        // creating dbi != dbj
        pushResult(surroundWithLambdas(app(neg(), tm), sortsFlex));

        if (sortsFlex[i].isBoolSort()) {
          // creating dbi \/ dbj
          pushResult(surroundWithLambdas(app(disj(), {dbi, dbj}), sortsFlex));

          // creating dbi /\ dbj
          pushResult(surroundWithLambdas(app(conj(), {dbi, dbj}), sortsFlex));
        }
      }
    }

    // bind head variable to all general bindings produced using heads in _heads
    for (const auto& head : _heads) {

      bool surround = (!head.isProxy(Proxy::EQUALS) || !include_not_eq);
      TermList gb  = HOL::createGeneralBinding(head,sortsFlex,_freshVar,surround);
      pushResult(surround ? gb : surroundWithLambdas(gb, sortsFlex));

      if (!surround) {
        // add not equals
        pushResult(surroundWithLambdas(app(neg(), gb), sortsFlex));
      }
    }

    return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
  }

private:
  TermStack _heads;
  Clause* _cl;
  unsigned _freshVar;
  const Options::PISet _piSet;
};

PrimitiveInstantiation::PrimitiveInstantiation(SaturationAlgorithm& salg) : _piSet(salg.getOptions().piSet()) {}

ClauseIterator PrimitiveInstantiation::generateClauses(Clause* premise)
{
  // TODO is doing this only on selected literals correct?
  return pvi(premise->getSelectedLiteralIterator()
    .filter([](Literal* l) { return l->isFlexRigid() && SortHelper::getEqualityArgumentSort(l).isBoolSort(); })
    .flatMap(PrimitiveInstResultFn(premise, _piSet)));
}

}
