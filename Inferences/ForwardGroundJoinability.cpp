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
 * @file ForwardGroundJoinability.cpp
 * Implements class ForwardGroundJoinability.
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

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "DemodulationHelper.hpp"

#include "ForwardGroundJoinability.hpp"

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

void ForwardGroundJoinability::attach(SaturationAlgorithm* salg)
{
  ForwardGroundSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );
}

void ForwardGroundJoinability::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardGroundSimplificationEngine::detach();
}

bool toTheLeftStrict(const Position& p1, const Position& p2)
{
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return false;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  return false;
}

TermList replace(TermList t, TermList from, TermList to)
{
  if (t == from) {
    return to;
  }
  if (t.isVar()) {
    return t;
  }
  return TermList(EqHelper::replace(t.term(), from, to));
}

std::pair<ForwardGroundJoinability::State*,const TermPartialOrdering*> ForwardGroundJoinability::getNext(
  RedundancyCheck& checker, State* curr, Stack<TermOrderingConstraint> cons, TermList left, TermList right, Position pos)
{
  if (left == right) {
    return checker.next(cons, nullptr);
  }
  bool L = curr->L && curr->left == left;
  bool R = curr->R && curr->right == right;
  _states.push(new State{ left, right, L, R, pos });
  return checker.next(cons, _states.top());
}

bool ForwardGroundJoinability::perform(Clause* cl, ClauseIterator& replacements, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  static DHSet<TermList> attempted;

  // we do not support AVATAR yet
  if (!cl->noSplits() || cl->length()>1) {
    return false;
  }

  auto clit = (*cl)[0];
  if (!clit->isEquality() || clit->isNegative()) {
    return false;
  }
  DHSet<Clause*> premiseSet;
  DHMap<std::pair<TermList,TermList>,OrderingComparator::VarOrderExtractor> extractors;

  // cleanup previous states
  while (_states.isNonEmpty()) {
    delete _states.pop();
  }

  auto curr = new State{
    clit->termArg(0), clit->termArg(1), true, true, Position()
  };

  _states.push(curr);
  RedundancyCheck checker(ordering, curr);
  auto tpo = TermPartialOrdering::getEmpty(ordering);
  unsigned cnt = 0;

  while (curr) {
    if (cnt++ > 500) {
      return false;
    }
    attempted.reset();

    Stack<TermOrderingConstraint> eqCons;
    if (makeEqual(curr->left, curr->right, eqCons)) {
      auto kv = checker.next(eqCons, nullptr);
      curr = kv.first;
      tpo = kv.second;
      if (!curr) {
        break;
      }
    }

    ASS(!tpo->hasIncomp());

    NonVariableNonTypeIterator it(curr->left, curr->right);
    while (it.hasNext()) {
      TermList trm(it.next());
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }
      // if the position is to the left, we have already tried it
      //
      // TODO: this is not perfect as some terms we try and fail
      // due to the extension of TPO in ordering being imperfect
      auto pos = it.currPos();
      if (toTheLeftStrict(pos, curr->pos)) {
        continue;
      }

      bool redundancyCheck = _redundancyCheck &&
        ((curr->L && trm == curr->left) ||
         (curr->R && trm == curr->right));

      auto git = _index->getGeneralizations(trm.term(), /* retrieveSubstitutions */ true);
      while(git.hasNext()) {
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

        TermList rhs = qr.data->rhs;

        auto subs = qr.unifier;
        ASS(subs->isIdentityOnQueryWhenResultBound());

        Applicator appl(subs.ptr());

        POStruct po_struct(tpo);

        // qr.data->comparator->init(&appl);
        // if (!qr.data->comparator->next(&po_struct)) {
        //   continue;
        // }

#if VDEBUG
        POStruct dpo_struct(tpo);
        OrderingComparator::VarOrderExtractor2 extractor(ordering, qr.data->term, qr.data->rhs, &appl, dpo_struct);
        std::pair<Result,POStruct> kv { Ordering::INCOMPARABLE, nullptr };
        do {
          kv = extractor.next();
        } while (kv.second.tpo && kv.first != Ordering::GREATER);
#endif

        if (!qr.data->comparator->extractVarOrder(&appl, po_struct)) {
          ASS_NEQ(kv.first, Ordering::GREATER);
          continue;
        }
        ASS_EQ(kv.first, Ordering::GREATER);
        // ASS_EQ(kv.second.tpo, po_struct.tpo);

        // encompassing demodulation is fine when rewriting the smaller guy
        if (redundancyCheck) {
          // this will only run at most once;
          // could have been factored out of the getGeneralizations loop,
          // but then it would run exactly once there
          Ordering::Result litOrder = ordering.compare(curr->left,curr->right);
          if ((trm==curr->left && litOrder == Ordering::LESS) ||
              (trm==curr->right && litOrder == Ordering::GREATER)) {
            redundancyCheck = false;
          }
        }

        AppliedTerm rhsApplied(rhs, &appl, true);

#if VDEBUG
        auto dcomp = ordering.createComparator(false, false, po_struct.tpo);
        dcomp->insert({ { trm, rhsApplied.apply(), Ordering::GREATER } }, (void*)0x1);
        ASS(dcomp->checkAndCompress());
#endif

        if (redundancyCheck && (!_encompassing || DemodulationHelper::isRenamingOn(&appl,lhs))) {
          TermList other = trm == curr->left ? curr->right : curr->left;
          auto redComp = ordering.compareUnidirectional(other, rhsApplied, &po_struct);
          ASS_NEQ(redComp,Ordering::LESS);
          // Note: EQUAL should be fine when doing forward simplification
          if (((curr->L && curr->R) || redComp != Ordering::EQUAL) && redComp != Ordering::GREATER) {
            continue;
          }
#if VDEBUG
          dcomp = ordering.createComparator(false, false, po_struct.tpo);
          dcomp->insert({ { other, rhsApplied.apply(), Ordering::GREATER } }, (void*)0x1);
          if (!curr->L || !curr->R) {
            dcomp->insert({ { other, rhsApplied.apply(), Ordering::EQUAL } }, (void*)0x1);
          }
          ASS(dcomp->checkAndCompress());
#endif
        }

        TermList rhsS = rhsApplied.apply();

        auto left = replace(curr->left, trm, rhsS);
        auto right = replace(curr->right, trm, rhsS);

        auto next = getNext(checker, curr, po_struct.cons, left, right, pos);
        // TODO can it be that we go to a different node in the tree and get the same result still?
        ASS(next.first != curr || next.second != tpo);
        curr = next.first;
        tpo = next.second;
        premiseSet.insert(qr.data->clause);
        goto LOOP_END;
      }
    }
    return false;
LOOP_END:
    continue;
  }
  premises = pvi(getPersistentIterator(premiseSet.iterator()));

  env.statistics->forwardGroundJoinability++;
  return true;
}

ForwardGroundJoinability::RedundancyCheck::RedundancyCheck(const Ordering& ord, State* data)
  : comp(ord.createComparator(/*onlyVars=*/true, /*ground=*/true))
{
  comp->_source = Branch(data, comp->_sink);
  comp->_source.node()->ready = true;
  path.push(&comp->_source);
}

std::pair<ForwardGroundJoinability::State*,const TermPartialOrdering*> ForwardGroundJoinability::RedundancyCheck::next(
  Stack<TermOrderingConstraint> ordCons, State* data)
{
  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };
  ASS(path.isNonEmpty());

  auto curr = path.top();
  ASS_EQ(curr->node()->tag, Tag::T_DATA);
  ASS(curr->node()->data);
  ASS(curr->node()->ready);
  ASS_EQ(curr->node()->refcnt,1);

  // current node has to be processed again
  curr->node()->ready = false;

  // We replace (not modify) the current node
  // with a new subtree containing ordCons and data
  // and pointing to the original node otherwise.

  Branch origB(*curr);
  Branch newB = data ? Branch(data, comp->_sink) : comp->_sink;

  for (const auto& [lhs,rhs,rel] : ordCons) {
    ASS(lhs.isVar());
    ASS(rhs.isVar());
    *curr = Branch(lhs, rhs);
    for (unsigned i = 0; i < 3; i++) {
      if (ordVals[i] != rel) {
        curr->node()->getBranch(ordVals[i]) = origB;
      }
    }
    curr = &curr->node()->getBranch(rel);
  }
  *curr = newB;

  while (path.isNonEmpty()) {
    comp->_prev = path.size()==1 ? nullptr : path[path.size()-2];
    comp->_curr = path.top();
    comp->processCurrentNode();

    auto node = comp->_curr->node();
    if (node->tag == Tag::T_DATA && !node->data) {
      pushNext();
      continue;
    }

    // there shouldn't be any invalid branches here
    ASS(node->trace && !node->trace->hasIncomp());

    if (node->tag == Tag::T_DATA) {
      ASS(node->data);
      return make_pair(static_cast<State*>(node->data), node->trace);
    }
    path.push(&node->gtBranch);
  }

  ASS(path.isEmpty());
  return { nullptr, nullptr };
}

void ForwardGroundJoinability::RedundancyCheck::pushNext()
{
  while (path.isNonEmpty()) {
    auto curr = path.pop();
    if (path.isEmpty()) {
      continue;
    }

    auto prev = path.top()->node();
    ASS_EQ(prev->tag, Tag::T_TERM);
    // if there is a previous node and we were either in the gt or eq
    // branches, just go to next branch in order, otherwise backtrack
    if (curr == &prev->gtBranch) {
      path.push(&prev->eqBranch);
      break;
    }
    if (curr == &prev->eqBranch) {
      path.push(&prev->ngeBranch);
      break;
    }
  }
}

bool ForwardGroundJoinability::makeEqual(TermList lhs, TermList rhs, Stack<TermOrderingConstraint>& res)
{
  if (lhs == rhs) {
    return true;
  }
  if (lhs.isVar()!=rhs.isVar()) {
    return false;
  }
  if (lhs.isVar() && rhs.isVar()) {
    res.push({ lhs, rhs, Ordering::EQUAL });
    return true;
  }
  auto lhsT = lhs.term();
  auto rhsT = rhs.term();
  if (lhsT->functor()!=rhsT->functor()) {
    return false;
  }
  SubtermIterator it1(lhs.term());
  SubtermIterator it2(rhs.term());
  while (it1.hasNext()) {
    ALWAYS(it2.hasNext());
    auto st1 = it1.next();
    auto st2 = it2.next();
    if (st1.isVar()!=st2.isVar()) {
      return false;
    }
    if (st1.isVar() && st2.isVar()) {
      res.push({ st1, st2, Ordering::EQUAL });
      continue;
    }
    if (st1.term()->functor()!=st2.term()->functor()) {
      return false;
    }
  }
  return true;
}

}