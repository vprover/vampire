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
 * @file ForwardGroundReducibility.cpp
 * Implements class ForwardGroundReducibility.
 */

#include "Lib/DHSet.hpp"
#include "Lib/Environment.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ColorHelper.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/ConditionalRedundancyHandler.hpp"
#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "DemodulationHelper.hpp"
#include "ForwardGroundJoinability.hpp"

#include "ForwardGroundReducibility.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;
using namespace std;

namespace {

struct Applicator : SubstApplicator {
  Applicator(ResultSubstitution* subst) : subst(subst) {}
  TermList operator()(unsigned v) const override {
    return subst->applyToBoundResult(v);
  }
  ResultSubstitution* subst;
};

} // end namespace

void ForwardGroundReducibility::attach(SaturationAlgorithm* salg)
{
  ForwardGroundSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void ForwardGroundReducibility::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardGroundSimplificationEngine::detach();
}

bool ForwardGroundReducibility::perform(Clause* cl, ClauseIterator& replacements, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;
  attempted.reset();

  DHSet<tuple<TermList,TermList,Clause*>> results;

  auto res = ClauseIterator::getEmpty();
  _comp = ordering.createComparator(/*onlyVars=*/true, /*ground=*/true);
  _path.reset();
  _path.push(&_comp->_source);

  auto tpo = TermPartialOrdering::getEmpty(ordering);

  for (unsigned i = 0; i < cl->length(); i++) {
    auto clit = (*cl)[i];
    if (clit->isEquality() && clit->isPositive()) {
      Stack<TermOrderingConstraint> eqCons;
      if (ForwardGroundJoinability::makeEqual(clit->termArg(0), clit->termArg(1), eqCons)) {
        tpo = next(eqCons);
        if (!tpo) {
          // this shouldn't happen though
          return true;
        }
      }
    }
  }

  bool clRedCheck = cl->length()==1 && (*cl)[0]->isPositive() && (*cl)[0]->isEquality();

  while (tpo) {
    for (unsigned i = 0; i < cl->length(); i++) {
      auto clit = (*cl)[i];
      NonVariableNonTypeIterator it(clit);
      while (it.hasNext()) {
        TermList trm(it.next());
        if (!attempted.insert(trm)) {
          it.right();
          continue;
        }
        bool redundancyCheck = false;
        if (clRedCheck && trm == clit->termArg(0) && ordering.getEqualityArgumentOrder(clit) != Ordering::LESS) {
          redundancyCheck = true;
        }
        if (clRedCheck && trm == clit->termArg(1) && ordering.getEqualityArgumentOrder(clit) != Ordering::GREATER) {
          redundancyCheck = true;
        }

        auto git = _index->getGeneralizations(trm.term(), /* retrieveSubstitutions */ true);
        while (git.hasNext()) {
          auto qr=git.next();
          ASS_EQ(qr.data->clause->length(),1);

          auto lhs = qr.data->term;
          if (lhs.isVar()) {
            // we are not interested in these for now
            continue;
          }

          auto subs = qr.unifier;
          ASS(subs->isIdentityOnQueryWhenResultBound());
          Applicator appl(subs.ptr());
          
          POStruct po_struct(tpo);

          qr.data->comparator->init(&appl);
          if (!qr.data->comparator->next(&po_struct)) {
            continue;
          }

          AppliedTerm rhsApplied(qr.data->rhs, &appl, true);

          if (redundancyCheck && DemodulationHelper::isRenamingOn(&appl,lhs)) {
            TermList other = EqHelper::getOtherEqualitySide(clit, trm);
            auto redComp = ordering.compareUnidirectional(other, rhsApplied, &po_struct);
            if (redComp != Ordering::GREATER) {
              continue;
            }
          }

          tpo = next(po_struct.cons);
          results.insert({ trm, rhsApplied.apply(), qr.data->clause });
          goto LOOP_END;
        }
      }
    }
    return false;
LOOP_END:
    continue;
  }

  DHSet<tuple<TermList,TermList,Clause*>>::Iterator rit(results);
  while (rit.hasNext()) {
    auto result = rit.next();
    RStack<Literal*> resLits;
    for(unsigned i=0;i<cl->length();i++) {
      resLits->push(EqHelper::replace((*cl)[i],get<0>(result),get<1>(result)));
    }

    auto resCl = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_GROUND_REDUCIBILITY, cl, get<2>(result)));
    res = pvi(concatIters(res,getSingletonIterator(resCl)));
    premises = pvi(concatIters(premises,getSingletonIterator(get<2>(result)))); // this gives duplicates
  }

  env.statistics->forwardGroundReducibility++;
  replacements = res;
  return true;
}

const TermPartialOrdering* ForwardGroundReducibility::next(OrderingConstraints ordCons)
{
  ASS(_comp->_ground);
  ASS(_comp->_onlyVars);

  using Node = OrderingComparator::Node;
  using Branch = OrderingComparator::Branch;

  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };
  ASS(_path.isNonEmpty());

  auto curr = _path.top();
  ASS_EQ(curr->node(), _comp->_sink.node());

  // We replace (not modify) the current node
  // with a new subtree containing ordCons and data
  // and pointing to the original node otherwise.

  Branch success = Branch(this, _comp->_sink);

  for (const auto& [lhs,rhs,rel] : ordCons) {
    ASS(lhs.isVar());
    ASS(rhs.isVar());
    *curr = Branch(lhs, rhs);
    for (unsigned i = 0; i < 3; i++) {
      if (ordVals[i] != rel) {
        curr->node()->getBranch(ordVals[i]) = _comp->_sink;
      }
    }
    curr = &curr->node()->getBranch(rel);
  }
  *curr = success;

  while (_path.isNonEmpty()) {
    _comp->_prev = _path.size()==1 ? nullptr : _path[_path.size()-2];
    _comp->_curr = _path.top();
    _comp->processCurrentNode();
    auto node = _comp->_curr->node();

    if (node->tag != Node::T_DATA) {
      _path.push(&node->gtBranch);
      continue;
    }

    if (!node->data) {
      ASS(!node->trace);
      return _comp->getCurrentTrace();
    }

    pushNext();
  }

  ASS(_path.isEmpty());
  return nullptr;
}


void ForwardGroundReducibility::pushNext()
{
    while (_path.isNonEmpty()) {
      auto curr = _path.pop();
      if (_path.isEmpty()) {
        continue;
      }

      auto prev = _path.top()->node();
    ASS_EQ(prev->tag, OrderingComparator::Node::T_TERM);
      // if there is a previous node and we were either in the gt or eq
      // branches, just go to next branch in order, otherwise backtrack
      if (curr == &prev->gtBranch) {
        _path.push(&prev->eqBranch);
        break;
      }
      if (curr == &prev->eqBranch) {
        _path.push(&prev->ngeBranch);
        break;
      }
    }
}

}