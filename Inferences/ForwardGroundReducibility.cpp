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

#include <set>

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
  // we do not support AVATAR yet
  if (!cl->noSplits()) {
    return false;
  }

  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;
  DHMap<std::pair<TermList,TermList>,OrderingComparator::VarOrderExtractor> extractors;

  // TODO investigate source of nondeterminism here

  // we need consistent order of results so we use an STL set
  std::set<std::tuple<TermList,TermList,Clause*>> results;

  auto res = ClauseIterator::getEmpty();
  _comp = ordering.createComparator(/*onlyVars=*/true, /*ground=*/true);
  _path.reset();
  _path.push(&_comp->_source);

  auto tpo = TermPartialOrdering::getEmpty(ordering);

  for (unsigned i = 0; i < cl->length(); i++) {
    auto clit = (*cl)[i];
    if (!clit->isEquality() || clit->isNegative()) {
      continue;
    }
    Stack<TermOrderingConstraint> eqCons;
    if (!ForwardGroundJoinability::makeEqual(clit->termArg(0), clit->termArg(1), eqCons)) {
      continue;
    }
    tpo = next(eqCons);
    if (!tpo) {
      // this shouldn't happen though
      return true;
    }
  }

  bool fail = false;
  bool clRedCheck = _redundancyCheck && cl->length()==1 &&
    (*cl)[0]->isPositive() && (*cl)[0]->isEquality();

  while (tpo) {
    for (unsigned i = 0; i < cl->length(); i++) {
      auto clit = (*cl)[i];
      attempted.reset();
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
          // we do not support AVATAR yet
          if (!qr.data->clause->noSplits()) {
            continue;
          }

          auto subs = qr.unifier;
          ASS(subs->isIdentityOnQueryWhenResultBound());
          Applicator appl(subs.ptr());

          POStruct po_struct(tpo);

          // qr.data->comparator->init(&appl);
          // if (!qr.data->comparator->next(&po_struct)) {
          //   continue;
          // }

          AppliedTerm rhsApplied(qr.data->rhs, &appl, true);

#if VDEBUG
          POStruct dpo_struct(tpo);
          OrderingComparator::VarOrderExtractor::Iterator dextIt(ordering, trm, rhsApplied.apply(), dpo_struct);
          std::pair<Result,POStruct> kv { Ordering::INCOMPARABLE, nullptr };
          do {
           kv = dextIt.next();
          } while (kv.second.tpo && kv.first != Ordering::GREATER);
#endif

          bool nodebug = false;
          OrderingComparator::VarOrderExtractor extractor(qr.data->comparator.get(), &appl, po_struct);
          if (!extractor.hasNext(nodebug)) {
            ASS(nodebug || kv.first != Ordering::GREATER);
            continue;
          }
          po_struct = extractor.next();
          ASS(nodebug || kv.first == Ordering::GREATER);
          // TODO for some rather complicated reason this sometimes
          // fail as the two extractors take two different branches
          // ASS(nodebug || kv.second.tpo == po_struct.tpo);

#if VDEBUG
          auto dcomp = ordering.createComparator(false, false, po_struct.tpo);
          dcomp->insert({ { trm, rhsApplied.apply(), Ordering::GREATER } }, (void*)0x1);
          ASS(dcomp->checkAndCompress());
#endif

          if (redundancyCheck && (!_encompassing || DemodulationHelper::isRenamingOn(&appl,lhs))) {
            TermList other = EqHelper::getOtherEqualitySide(clit, trm);
            auto redComp = ordering.compareUnidirectional(other, rhsApplied, &po_struct);
            if (redComp != Ordering::GREATER) {
              continue;
            }
#if VDEBUG
            dcomp = ordering.createComparator(false, false, po_struct.tpo);
            dcomp->insert({ { other, rhsApplied.apply(), Ordering::GREATER } }, (void*)0x1);
            ASS(dcomp->checkAndCompress());
#endif
          }

          tpo = next(po_struct.cons);
          results.insert({ trm, rhsApplied.apply(), qr.data->clause });
          goto LOOP_END;
        }
      }
    }
    if (cl->store()==Clause::SELECTED) {
      tpo = skip();
      fail = true;
    } else {
      return false;
    }
LOOP_END:
    continue;
  }

  if (fail && results.size()==0) {
    return false;
  }

  for (const auto& [lhs,rhs,demodulator] : results) {
    RStack<Literal*> resLits;
    for(unsigned i=0;i<cl->length();i++) {
      resLits->push(EqHelper::replace((*cl)[i],lhs,rhs));
    }

    auto resCl = Clause::fromStack(*resLits, SimplifyingInference2(InferenceRule::FORWARD_GROUND_REDUCIBILITY, cl, demodulator));
    auto infTod = ordering.createComparator(true, true).release();
    OrderingConstraints ordCons;
    ordCons.push({ lhs, rhs, Ordering::GREATER });
    infTod->insert(ordCons, resCl);
    resCl->setInfTod(infTod);
    res = pvi(concatIters(res,getSingletonIterator(resCl)));
    premises = pvi(concatIters(premises,getSingletonIterator(demodulator))); // this gives duplicates
  }

  ALWAYS(fail != _comp->checkAndCompress());

  if (fail) {
    delete static_cast<OrderingComparator*>(cl->getTod());
    cl->setTod(_comp.release());
    res = pvi(concatIters(res,getSingletonIterator(cl)));
  } else {
    env.statistics->forwardGroundReducibility++;
  }
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
        curr->node()->getBranchUnsafe(ordVals[i]) = _comp->_sink;
      }
    }
    curr = &curr->node()->getBranchUnsafe(rel);
  }
  *curr = success;

  while (_path.isNonEmpty()) {
    _comp->_prev = _path.size()==1 ? nullptr : _path[_path.size()-2];
    _comp->_curr = _path.top();
    _comp->processCurrentNode();
    auto node = _comp->_curr->node();

    if (node->tag != Node::T_DATA) {
      _path.push(&node->getBranch(Ordering::GREATER));
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

const TermPartialOrdering* ForwardGroundReducibility::skip()
{
  ASS(_comp->_ground);
  ASS(_comp->_onlyVars);

  using Node = OrderingComparator::Node;

  ASS(_path.isNonEmpty());
  ASS_EQ(_path.top()->node()->tag,Node::T_DATA);
  ASS(!_path.top()->node()->data);

  pushNext();

  while (_path.isNonEmpty()) {
    _comp->_prev = _path.size()==1 ? nullptr : _path[_path.size()-2];
    _comp->_curr = _path.top();
    _comp->processCurrentNode();
    auto node = _comp->_curr->node();

    if (node->tag != Node::T_DATA) {
      _path.push(&node->getBranch(Ordering::GREATER));
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
    if (curr == &prev->getBranch(Ordering::GREATER)) {
      _path.push(&prev->getBranch(Ordering::EQUAL));
      break;
    }
    if (curr == &prev->getBranch(Ordering::EQUAL)) {
      _path.push(&prev->getBranch(Ordering::LESS));
      break;
    }
  }
}

}