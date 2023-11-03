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

#include "Debug/RuntimeStatistics.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/IndexManager.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "ForwardGroundJoinability.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace std;

inline TermList replace(TermList t, TermList what, TermList by) {
  if (t == what) {
    return by;
  }
  if (t.isVar()) {
    return t;
  }
  return TermList(EqHelper::replace(t.term(), what, by));
}

// TODOs:
// - reduce top-level terms modulo completeness check
// - make harder effort in KBO to extend the order (now it is based on orienting x > y if these are directly compared)
// - try doing the same in LPO
// - apply equalities from variable order
// - improve normalisation/extension by skipping terms already checked
// - implement backward variant
// - add option to switch (what about demodulation options? encompassment? preordered?)
// - pass variable orders and underlying triangular arrays more efficiently (e.g. recycle them)

void ForwardGroundJoinability::attach(SaturationAlgorithm* salg)
{
  ForwardSimplificationEngine::attach(salg);
  _index=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_CODE_TREE) );

  _preorderedOnly = getOptions().forwardDemodulation()== Options::Demodulation::PREORDERED;
  _redundancyCheck = getOptions().demodulationRedundancyCheck() != Options::DemodulationRedunancyCheck::OFF;
  _encompassing = getOptions().demodulationRedundancyCheck() == Options::DemodulationRedunancyCheck::ENCOMPASS;
}

void ForwardGroundJoinability::detach()
{
  _index=0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_CODE_TREE);
  ForwardSimplificationEngine::detach();
}

bool ForwardGroundJoinability::perform(Clause* cl, Clause*& replacement, ClauseIterator& premises)
{
  TIME_TRACE("forward ground joinability");
  const bool checkCompleteness = cl->length()==1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive();

  for (unsigned i = 0; i < cl->length(); i++) {
    auto lit = (*cl)[i];
    if (!lit->isEquality() || lit->ground()) {
      continue;
    }
    _premises.reset();
    auto s = lit->termArg(0);
    auto t = lit->termArg(1);
    if (join(s,t,checkCompleteness)) {
      env.statistics->forwardGroundJoinableEqs++;
      premises = pvi(iterTraits(_premises.iterator()).persistent());

      if (lit->isNegative()) {
        auto clen = cl->length()-1;
        auto prems = UnitList::empty();
        UnitList::pushFromIterator(_premises.iterator(), prems);
        UnitList::push(cl, prems);

        Clause* res = new(clen) Clause(clen,
          SimplifyingInferenceMany(InferenceRule::FORWARD_GROUND_JOINABILITY, prems));

        unsigned j = 0;
        for (unsigned l = 0; l < clen; l++) {
          Literal* curr=(*cl)[l];
          if (curr != lit) {
            (*res)[j++] = curr;
          }
        }
        replacement = res;
        ASS_EQ(j,clen);
      }
      return true;
    }
  }

  return false;
}

bool ForwardGroundJoinability::join(TermList s, TermList t, bool checkCompleteness)
{
  // cout << endl << "joining " << s << " = " << t << endl;
  const auto& ord = _salg->getOrdering();
  pair<bool,bool> cflags;
  if (checkCompleteness) {
    switch (ord.compare(s,t)) {
      case Ordering::GREATER:
      case Ordering::GREATER_EQ:
        cflags = make_pair(true,false);
        break;
      case Ordering::LESS:
      case Ordering::LESS_EQ:
        cflags = make_pair(false,true);
        break;
      case Ordering::INCOMPARABLE:
        cflags = make_pair(true,true);
        break;
      case Ordering::EQUAL:
        ASSERTION_VIOLATION;
    }
  } else {
    cflags = make_pair(false,false);
  }

  DHSet<unsigned> vars;
  vars.loadFromIterator(iterTraits(vi(new VariableIterator(s))).map([](TermList v) { return v.var(); }));
  vars.loadFromIterator(iterTraits(vi(new VariableIterator(t))).map([](TermList v) { return v.var(); }));

  Stack<State> todo;
  todo.push(State {
    .vo = VarOrder(),
    .s = s,
    .t = t,
    .cflags = cflags,
  });
  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    auto& c = curr.cflags;
    normalise(curr.s, curr.t, curr.vo, c.first, c.second);
    if (curr.s == curr.t) {
      continue;
    }
    // found a total variable preorder under which the terms don't join
    if (curr.vo.is_total(vars.size())) {
      return false;
    }
    TermList sp = curr.s;
    TermList tp = curr.t;
    auto cp = c;
    // we have to extend vo via some rewrite
    bool joined = false;
    VarOrder ext = curr.vo;
    while (extend(sp, cp.first, ext) || extend(tp, cp.second, ext)) {
      normalise(sp, tp, ext, cp.first, cp.second);
      if (sp == tp) {
        joined = true;
        // cout << "removing " << ext.to_string() << endl
        //      << "from " << curr.vo.to_string() << endl;
        auto vos = order_diff(curr.vo,ext);
        for (const auto& evo : vos) {
          VarOrder::EqApplicator voApp(evo);
          todo.push(State {
            .vo = evo,
            .s = SubstHelper::apply(curr.s,voApp),
            .t = SubstHelper::apply(curr.t,voApp),
            .cflags = c,
          });
        }
        // cout << endl;
        break;
      }
      // curr.vo = ext; // TODO this is in the pseudocode, although I think incorrectly
    }
    if (!joined) {
      return false;
    }
  }
  // cout << "could join " << s << " and " << t << endl;
  return true;
}

void ForwardGroundJoinability::normalise(TermList& s, TermList& t, const VarOrder& vo, bool& cc_s, bool& cc_t)
{
  TIME_TRACE("joinability normalise");
  const auto& ord = _salg->getOrdering();
  DHMap<Term*,TermList> cache;
  bool reduced = false;
  static TermList empty;
  empty.makeEmpty();

  do {
    reduced = false;
    NonVariableNonTypeIterator it(s, t, false, false/* , !checkCompleteness */); // TODO top-level rewrites with completeness check
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      TermList* cptr;
      if (!cache.getValuePtr(trm.term(),cptr,empty)) {
        // term has been checked and not reducible
        if (cptr->isEmpty()) {
          continue;
        }
        // no need to add reducing clause to premises since we have already added it
        s = replace(s,trm,*cptr);
        t = replace(t,trm,*cptr);
        reduced = true;
        // checkCompleteness = false;
        break;
      }

      TermQueryResultIterator git = _index->getGeneralizations(trm, true);
      while (git.hasNext()) {
        TermQueryResult qr = git.next();
        if (!qr.clause->noSplits()) {
          continue;
        }

        static RobSubstitution subst;
        bool resultTermIsVar = qr.term.isVar();
        if(resultTermIsVar){
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if(!subst.match(eqSort, 0, querySort, 1)){
            continue;
          }
        }

        TermList rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS = qr.substitution->applyToBoundResult(rhs);
        if (resultTermIsVar) {
          rhsS = subst.apply(rhsS, 0);
        }

        // cout << "checking " << trm << " >? " << rhsS << " under " << vo.to_string() << endl;
        if (!ord.isGreater(trm,rhsS,vo)) {
          // cout << "trm " << trm << " > " << rhsS << " under " << vo.to_string() << endl;
          continue;
        }
        ASS_REP(!vo.is_empty() || ord.compare(trm,rhsS)==Ordering::GREATER, trm.toString() + " not greater than " + rhsS.toString());

        s = replace(s,trm,rhsS);
        t = replace(t,trm,rhsS);
        reduced = true;
        // checkCompleteness = false;
        _premises.insert(qr.clause);
        *cptr = rhsS;
        break;
      }
      if (reduced) {
        break;
      }
    }
  } while (reduced);
}

bool ForwardGroundJoinability::extend(TermList& t, bool& checkCompleteness, VarOrder& ext)
{
  TIME_TRACE("joinability extend");
  // cout << "extending " << t << " under " << ext.to_string() << " completeness " << checkCompleteness << endl;
  const auto& ord = _salg->getOrdering();
  DHSet<Term*> attempted;
  if (t.isVar()) {
    return false;
  }
  NonVariableNonTypeIterator it(t.term()/* , !checkCompleteness */); // TODO top-level rewrites with completeness check
  while(it.hasNext()) {
    TypedTermList trm = it.next();
    if (!attempted.insert(trm.term())) {
      it.right();
      continue;
    }

    TermQueryResultIterator git = _index->getGeneralizations(trm, true);
    while (git.hasNext()) {
      TermQueryResult qr = git.next();
      if (!qr.clause->noSplits()) {
        continue;
      }

      static RobSubstitution subst;
      bool resultTermIsVar = qr.term.isVar();
      if(resultTermIsVar){
        TermList querySort = trm.sort();
        TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
        subst.reset();
        if(!subst.match(eqSort, 0, querySort, 1)){
          continue;
        }
      }

      TermList rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
      TermList rhsS = qr.substitution->applyToBoundResult(rhs);
      if (resultTermIsVar) {
        rhsS = subst.apply(rhsS, 0);
      }

      VarOrder temp = ext;
      if (ord.makeGreater(trm,rhsS,temp)) {
        t = replace(t,trm,rhsS);
        // cout << "extended the order to " << temp.to_string() << " with eq " << *trm.term() << " = " << rhsS << endl;
        ext = temp;
        checkCompleteness = false;
        return true;
      }
    }
  }

  return false;
}

void ForwardGroundJoinability::order_diff_helper(VarOrder& vo, const List<Edge>* edges, Stack<VarOrder>& res)
{
  if (List<Edge>::isEmpty(edges)) {
    return;
  }

  auto e = edges->head();

  switch (e.c) {
    case PoComp::GT:
      if (vo.query(e.x,e.y) != PoComp::GT) {
        VarOrder eq = vo;
        VarOrder lt = vo;
        ALWAYS(eq.add_eq(e.x,e.y));
        ALWAYS(lt.add_gt(e.y,e.x));
        res.push(eq);
        res.push(lt);
        ALWAYS(vo.add_gt(e.x,e.y));
      }
      break;
    case PoComp::EQ:
      if (vo.query(e.x,e.y) != PoComp::EQ) {
        VarOrder gt = vo;
        VarOrder lt = vo;
        ALWAYS(gt.add_gt(e.x,e.y));
        ALWAYS(lt.add_gt(e.y,e.x));
        res.push(gt);
        res.push(lt);
        ALWAYS(vo.add_eq(e.x,e.y));
      }
      break;
    default:
      ASSERTION_VIOLATION;
  }

  order_diff_helper(vo, edges->tail(), res);

  // ignore (R.transitive_reduction var_order' |> List.fold_left (fun var_order_acc (x,ord,y) -> 
  //   (* TODO: is it possible that there are duplicate orders here? investigate closely *)
  //   let[@inline] get x y = VarOrder.query var_order_acc x y in
  //   let[@inline] gt x y = VarOrder.add_gt var_order_acc x y |> Option.get in
  //   let[@inline] eq x y = VarOrder.add_eq var_order_acc x y |> Option.get in
  //   match ord with
  //   | R.L_GT -> 
  //     if get x y != GT then (
  //       Stack.push (l, r, eq x y, complete) state.var_orders_eq; 
  //       Stack.push (l, r, gt y x, complete) state.var_orders_gt;
  //       gt x y
  //     ) else var_order_acc
  //   | R.L_EQ -> 
  //     if get x y != EQ then (
  //       Stack.push (l, r, gt x y, complete) state.var_orders_gt; 
  //       Stack.push (l, r, gt y x, complete) state.var_orders_gt;
  //       eq x y
  //     ) else var_order_acc
  //   (* dbg D_fw_gjoin @@ lazy (sprintf "              add: %s"  (VarOrder.to_string_dbg @@ List.nth result 0));
  //   dbg D_fw_gjoin @@ lazy (sprintf "              add: %s"  (VarOrder.to_string_dbg @@ List.nth result 1)); *)
  // ) var_order)
}

Stack<VarOrder> ForwardGroundJoinability::order_diff(const VarOrder& vo, const VarOrder& other)
{
  TIME_TRACE("order_diff");
  auto tr = other.transitive_reduction();

  Stack<VarOrder> res;
  VarOrder temp = vo;
  order_diff_helper(temp, tr, res);
  return res;
}

}
