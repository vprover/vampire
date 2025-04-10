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
#include "Kernel/TermOrderingDiagram.hpp"
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

#define ITERATION_LIMIT 500

bool ForwardGroundJoinability::perform(Clause* cl, ClauseIterator& premises)
{
  Ordering& ordering = _salg->getOrdering();

  // cout << "trying " << *cl << endl;

  static DHSet<TermList> attempted;

  if (cl->length()>1) {
    return false;
  }

  auto lit = (*cl)[0];
  if (!lit->isEquality() || lit->isNegative()) {
    return false;
  }
  DHSet<Clause*> premiseSet;

  if (EqHelper::isEqTautology(lit)) {
    premises = ClauseIterator::getEmpty();
    return true;
  }

  auto curr = lit;
  RedundancyCheck checker(ordering, curr);
  auto tpo = TermPartialOrdering::getEmpty(ordering);
  unsigned cnt = 0;

  while (curr) {
    if (cnt++ > ITERATION_LIMIT) {
      // cout << "failed due to iteration limit" << endl;
      return false;
    }
    attempted.reset();

    Stack<TermOrderingConstraint> eqCons;
    if (makeEqual(curr, eqCons)) {
      auto kv = checker.next(eqCons, nullptr);
      if (curr != kv.first || tpo != kv.second) {
        curr = kv.first;
        tpo = kv.second;
        continue;
      }
    }

    ASS(tpo->isGround());

    NonVariableNonTypeIterator it(curr);
    while (it.hasNext()) {
      TermList trm(it.next());
      if (!attempted.insert(trm)) {
        it.right();
        continue;
      }

      auto git = _index->getGeneralizations(trm.term(), /* retrieveSubstitutions */ true);
      while(git.hasNext()) {
        auto qr=git.next();
        ASS_EQ(qr.data->clause->length(),1);

        auto lhs = qr.data->term;
        if (lhs.isVar()) {
          // we are not interested in these for now
          continue;
        }
        // this is a random tiebreaker instead of the usual redundancy check
        if (qr.data->clause->number()>=cl->number()) {
          continue;
        }

        TermList rhs = qr.data->rhs;

        auto subs = qr.unifier;
        ASS(subs->isIdentityOnQueryWhenResultBound());
        Applicator appl(subs.ptr());

        AppliedTerm rhsApplied(rhs, &appl, true);

#if VDEBUG
        POStruct dpo_struct(tpo);
        TermOrderingDiagram::VarOrderExtractor::Iterator dextIt(ordering, trm, rhsApplied.apply(), dpo_struct);
        std::pair<Result,POStruct> kv { Ordering::INCOMPARABLE, nullptr };
        while (kv.first != Ordering::GREATER && dextIt.hasNext()) {
          kv = dextIt.next();
        }
#endif

        POStruct po_struct(tpo);
        bool nodebug = false;
        TermOrderingDiagram::VarOrderExtractor extractor(qr.data->tod.get(), &appl, po_struct);
        if (!extractor.hasNext(nodebug)) {
          ASS(nodebug || kv.first != Ordering::GREATER);
          continue;
        }
        po_struct = extractor.next();
        ASS(nodebug || kv.first == Ordering::GREATER);
        // TODO for some rather complicated reason this sometimes
        // fails as the two extractors take two different branches
        // ASS(nodebug || kv.second.tpo == po_struct.tpo);

        TermList rhsS = rhsApplied.apply();

        auto nextLit = EqHelper::replace(curr, trm, rhsS);
        auto next = checker.next(po_struct.cons, EqHelper::isEqTautology(nextLit) ? nullptr : nextLit);
        // TODO can it be that we go to a different node in the tree and get the same result still?
        ASS(next.first != curr || next.second != tpo);
        curr = next.first;
        tpo = next.second;
        premiseSet.insert(qr.data->clause);
        goto LOOP_END;
      }
    }
    // cout << "failed with " << *curr << endl << *tpo << endl;
    return false;
LOOP_END:
    continue;
  }
  premises = pvi(getPersistentIterator(premiseSet.iterator()));

  // cout << "forward ground joinable " << *cl << endl;

  env.statistics->forwardGroundJoinable++;
  return true;
}

ForwardGroundJoinability::RedundancyCheck::RedundancyCheck(const Ordering& ord, Literal* data)
  : tod(ord.createTermOrderingDiagram(/*ground=*/true)), traversal(tod.get())
{
  tod->_source = Branch(data, tod->_sink);
  tod->_source.node()->ready = true;
  _curr = &tod->_source;
}

std::pair<Literal*,const TermPartialOrdering*> ForwardGroundJoinability::RedundancyCheck::next(
  Stack<TermOrderingConstraint> ordCons, Literal* data)
{
  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };

  {
    auto curr = _curr;
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
    Branch newB = data ? Branch(data, tod->_sink) : tod->_sink;

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
  }

  if (!traversal._fresh) {
    traversal.processNode(_curr);
    auto node = _curr->node();
    if (node->tag == Tag::T_DATA) {
      if (node->data) {
        // there shouldn't be any invalid branches here
        ASS(node->trace && node->trace->isGround());
        return make_pair(static_cast<Literal*>(node->data), node->trace);
      }
    } else {
      traversal.goDown(_curr);
    }
  }

  while (traversal.hasNext()) {
    _curr = traversal.next();

    auto node = _curr->node();
    ASS_EQ(node->tag, Tag::T_DATA)
    if (node->data) {
      // there shouldn't be any invalid branches here
      ASS(node->trace && node->trace->isGround());
      return make_pair(static_cast<Literal*>(node->data), node->trace);
    }
  }

  return { nullptr, nullptr };
}

bool ForwardGroundJoinability::makeEqual(Literal* lit, Stack<TermOrderingConstraint>& res)
{
  ASS(lit->isEquality());
  ASS(lit->isPositive());
  auto lhs = lit->termArg(0);
  auto rhs = lit->termArg(1);
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
