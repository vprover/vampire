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

#define LOGGING 0

#if LOGGING
#define LOG1(s,arg) s << arg << endl;
#define LOG2(s,a1,a2) s << a1 << a2 << endl;
#define LOG3(s,a1,a2,a3) s << a1 << a2 << a3 << endl;
#define LOG4(s,a1,a2,a3,a4) s << a1 << a2 << a3 << a4 << endl;
#else
#define LOG1(s,arg)
#define LOG2(s,a1,a2)
#define LOG3(s,a1,a2,a3)
#define LOG4(s,a1,a2,a3,a4)
#endif

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
      // cout << "could join " << *cl << endl;

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

bool ForwardGroundJoinability::join(TermList orig_s, TermList orig_t, bool checkCompleteness)
{
  LOG4(cout,"joining ", orig_s, " and ", orig_t);
  const auto& ord = _salg->getOrdering();
  bool cc_s = false;
  bool cc_t = false;
  if (checkCompleteness) {
    switch (ord.compare(orig_s,orig_t)) {
      case Ordering::GREATER:
      case Ordering::GREATER_EQ:
        cc_s = true;
        break;
      case Ordering::LESS:
      case Ordering::LESS_EQ:
        cc_t = true;
        break;
      case Ordering::INCOMPARABLE:
        cc_s = true;
        cc_t = true;
        break;
      case Ordering::EQUAL:
        ASSERTION_VIOLATION;
    }
  }

  DHSet<unsigned> vars;
  vars.loadFromIterator(iterTraits(vi(new VariableIterator(orig_s))).map([](TermList v) { return v.var(); }));
  vars.loadFromIterator(iterTraits(vi(new VariableIterator(orig_t))).map([](TermList v) { return v.var(); }));

  Stack<State> todo;
  todo.push(State(VarOrder(),orig_s,orig_t,cc_s,cc_t,orig_s,orig_t));
  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    LOG2(cout,"join ",curr.toString());
    normalise(curr);
    if (curr.s == curr.t) {
      continue;
    }
    LOG2(cout,"normalised ",curr.toString());
    // found a total variable preorder under which the terms don't join
    if (curr.vo.is_total(vars.size())) {
      LOG2(cout,"total ",curr.toString());
      return false;
    }
    State ext = curr;
    // // we have to extend vo via some rewrite
    bool joined = false;
    while (extend(ext.s, ext.cc_s, ext.vo, ext.orig_t) || extend(ext.t, ext.cc_t, ext.vo, ext.orig_s)) {
      LOG2(cout,"extended ",ext.toString());
      normalise(ext);
      LOG2(cout,"normalised ",ext.toString());
      if (ext.s == ext.t) {
        LOG2(cout,"joined ",ext.toString());
        joined = true;
        auto vos = order_diff(curr.vo,ext.vo);
        for (auto&& evo : vos) {
          VarOrder::EqApplicator voApp(evo);
          todo.push(State(std::move(evo),
            SubstHelper::apply(curr.s,voApp),
            SubstHelper::apply(curr.t,voApp),
            curr.cc_s, curr.cc_t,
            SubstHelper::apply(curr.orig_s,voApp),
            SubstHelper::apply(curr.orig_t,voApp)));
        }
        break;
      }
    }
    if (!joined) {
      LOG2(cout,"could not join ",curr.toString());
      return false;
    }
  }
  return true;
}

void ForwardGroundJoinability::normalise(State& state)
{
  TIME_TRACE("joinability normalise");
  const auto& ord = _salg->getOrdering();
  // DHMap<Term*,TermList> cache;
  bool reduced = false;
  static TermList empty;
  empty.makeEmpty();

  do {
    // LOG2(cout,"normalising round ",state.toString());
    reduced = false;
    NonVariableNonTypeIterator it(state.s, state.t, true, true);
    while(it.hasNext()) {
      TypedTermList trm = it.next();
      // TermList* cptr;
      // if (!cache.getValuePtr(trm.term(),cptr,empty)) {
      //   // term has been checked and not reducible
      //   if (cptr->isEmpty()) {
      //     continue;
      //   }
      //   // no need to add reducing clause to premises since we have already added it
      //   s = replace(s,trm,*cptr);
      //   t = replace(t,trm,*cptr);
      //   reduced = true;
      //   // checkCompleteness = false;
      //   break;
      // }

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
        if (!ord.isGreater(trm,rhsS,state.vo)) {
          // cout << "trm " << trm << " > " << rhsS << " under " << vo.to_string() << endl;
          continue;
        }
        ASS_REP(!state.vo.is_empty() || ord.compare(trm,rhsS)==Ordering::GREATER, trm.toString() + " not greater than " + rhsS.toString());

        // check completeness
        if (state.cc_s && trm == state.s) {
          ASS_EQ(state.s,state.orig_s);
          if (!ord.isGreater(state.orig_t, rhsS, state.vo) && qr.substitution->isRenamingOn(qr.term,true /* we talk of result term */)) {
            // cout << "orig_t " << state.orig_t << " is not greater than " << rhsS << " under " << state.vo.to_string() << endl;
            continue;
          }
        }
        if (state.cc_t && trm == state.t) {
          ASS_EQ(state.t,state.orig_t);
          if (!ord.isGreater(state.orig_s, rhsS, state.vo) && qr.substitution->isRenamingOn(qr.term,true /* we talk of result term */)) {
            // cout << "orig_s " << state.orig_s << " is not greater than " << rhsS << " under " << state.vo.to_string() << endl;
            continue;
          }
        }

        auto new_s = replace(state.s,trm,rhsS);
        auto new_t = replace(state.t,trm,rhsS);
        if (new_s != state.s) {
          state.cc_s = false;
        }
        if (new_t != state.t) {
          state.cc_t = false;
        }
        state.s = new_s;
        state.t = new_t;
        reduced = true;
        _premises.insert(qr.clause);
        // *cptr = rhsS;
        break;
      }
      if (reduced) {
        break;
      }
    }
  } while (reduced);
}

bool ForwardGroundJoinability::extend(TermList& t, bool& checkCompleteness, VarOrder& ext, TermList other)
{
  TIME_TRACE("joinability extend");
  // cout << "extending " << t << " under " << ext.to_string() << " completeness " << checkCompleteness << endl;
  const auto& ord = _salg->getOrdering();
  DHSet<Term*> attempted;
  if (t.isVar()) {
    return false;
  }
  NonVariableNonTypeIterator it(t.term(), true);
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
      if (!ord.makeGreater(trm,rhsS,temp)) {
        continue;
      }

      // check completeness
      if (checkCompleteness && trm == t) {
        if (!ord.makeGreater(other, rhsS,temp) && qr.substitution->isRenamingOn(qr.term,true /* we talk of result term */)) {
          continue;
        }
      }
      t = replace(t,trm,rhsS);
      // cout << "extended the order to " << temp.to_string() << " with eq " << *trm.term() << " = " << rhsS << endl;
      ext = temp;
      checkCompleteness = false;
      return true;
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
