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
 * @file TermPartialOrdering.cpp
 * Implements class TermPartialOrdering.
 */

#include <cstring>
#include <iomanip>

#include "TermPartialOrdering.hpp"

namespace Kernel {

using namespace std;

// Helper functions

Result poCompToResult(PoComp c) {
  switch (c) {
    case PoComp::GREATER:
      return Result::GREATER;
    case PoComp::EQUAL:
      return Result::EQUAL;
    case PoComp::LESS:
      return Result::LESS;
    case PoComp::NGEQ:
    case PoComp::NLEQ:
    case PoComp::INCOMPARABLE:
      return Result::INCOMPARABLE;
    default:
      break;
  }
  ASSERTION_VIOLATION;
}

PoComp resultToPoComp(Result r, bool reversed) {
  switch (r) {
    case Result::GREATER:
      return reversed ? PoComp::LESS : PoComp::GREATER;
    case Result::EQUAL:
      return PoComp::EQUAL;
    case Result::LESS:
      return reversed ? PoComp::GREATER : PoComp::LESS;
    case Result::INCOMPARABLE:
      return reversed ? PoComp::NLEQ : PoComp::NGEQ;
  }
}

// TermPartialOrdering

bool TermPartialOrdering::get(TermList lhs, TermList rhs, Result& res, bool flag) const
{
  // comparable terms should be handled by caller
  ASS_EQ(_ord.compare(lhs,rhs),Ordering::INCOMPARABLE);
  // proper term pairs should be handled by caller 
  ASS(lhs.isVar() || rhs.isVar());

  if (lhs == rhs) {
    res = Result::EQUAL;
    return true;
  }
  if (flag && !(_nodes.find(lhs) && _nodes.find(rhs))) {
    return false;
  }
  PoComp val;
  bool reversed = false;
  // If one or two of the terms is not in the partial ordering,
  // we try to relate them through terms in the relation
  if (!_nodes.find(lhs) && !_nodes.find(rhs))
  {
    val = getTwoExternal(lhs, rhs);
  }
  else if (!_nodes.find(lhs))
  {
    ASS(_nodes.find(rhs));
    size_t y = getId(rhs);
    val = getOneExternal(lhs, y);
  }
  else if (!_nodes.find(rhs))
  {
    ASS(_nodes.find(lhs));
    size_t x = getId(lhs);
    val = getOneExternal(rhs, x);
    reversed = true;
  }
  // Otherwise we relate them directly assuming that
  // the relation is already transitively closed.
  else
  {
    size_t x = getId(lhs);
    size_t y = getId(rhs);
    reversed = x > y;
    if (reversed) {
      swap(x,y);
    }
    val = _po->get(x,y);
  }
  if (val == PoComp::UNKNOWN) {
    return false;
  }
  // TODO: we currently assume that the caller is
  // only interested in lhs ≱ rhs, so if we only
  // have lhs ≰ rhs, we do not return anything.
  if (reversed) {
    if (val == PoComp::NGEQ) {
      return false;
    }
    res = Ordering::reverse(poCompToResult(val));
    return true;
  } else {
    if (val == PoComp::NLEQ) {
      return false;
    }
    res = poCompToResult(val);
    return true;
  }
}

Ordering::Result TermPartialOrdering::get(TermList lhs, TermList rhs) const
{
  Result res;
  if (!get(lhs, rhs, res, true)) {
    return Ordering::INCOMPARABLE;
  }
  return res;
}

const TermPartialOrdering* TermPartialOrdering::getEmpty(const Ordering& ord)
{
  static TermPartialOrdering empty(ord);
  return &empty;
}

const TermPartialOrdering* TermPartialOrdering::set(const TermPartialOrdering* tpo, TermOrderingConstraint con)
{
  static DHMap<std::tuple<const TermPartialOrdering*, TermList, TermList, Result>, const TermPartialOrdering*> cache;
  const TermPartialOrdering** ptr;
  if (cache.getValuePtr(make_tuple(tpo, con.lhs, con.rhs, con.rel), ptr, nullptr)) {
    auto res = new TermPartialOrdering(*tpo);
    if (!res->set(con)) {
      delete res;
      *ptr = nullptr;
    } else {
      *ptr = res;
    }
  }
  return *ptr;
}

PoComp TermPartialOrdering::getOneExternal(TermList t, size_t idx) const
{
  PoComp res = PoComp::UNKNOWN;
  decltype(_nodes)::Iterator it(_nodes);
  while (it.hasNext()) {
    auto& e = it.next();
    if (e.value()==idx) {
      continue;
    }
    auto val = _po->get(e.value(),idx);
    if (val == PoComp::UNKNOWN) {
      continue;
    }
    auto comp = _ord.compare(t,e.key());
    switch (comp) {
      case Ordering::GREATER: {
        switch (val) {
          case PoComp::EQUAL:
          case PoComp::GREATER:
            // t > e ≥ x -> t > x
            ALWAYS(checkCompatibility(res, PoComp::GREATER, res));
            return res;
          case PoComp::NLEQ:
          case PoComp::INCOMPARABLE:
            // t > e ≰ x -> t ≰ x
            ALWAYS(checkCompatibility(res, PoComp::NLEQ, res));
            if (res == PoComp::INCOMPARABLE) {
              return res;
            }
          default:
            break;
        }
        break;
      }
      case Ordering::EQUAL: {
        return val;
      }
      case Ordering::LESS: {
        switch (val) {
          case PoComp::EQUAL:
          case PoComp::LESS:
            // t < e ≤ x -> t < x
            ALWAYS(checkCompatibility(res, PoComp::LESS, res));
            return res;
          case PoComp::NGEQ:
          case PoComp::INCOMPARABLE:
            // t < e ≱ x -> t ≱ x
            ALWAYS(checkCompatibility(res, PoComp::NGEQ, res));
            if (res == PoComp::INCOMPARABLE) {
              return res;
            }
          default:
            break;
        }
        break;
      }
      case Ordering::INCOMPARABLE: {
        break;
      }
    }
  }
  return res;
}

PoComp TermPartialOrdering::getTwoExternal(TermList t1, TermList t2) const
{
  PoComp res = PoComp::UNKNOWN;
  Stack<pair<size_t,Ordering::Result>> t1_rel; // ∃x. t1 rel x
  Stack<pair<size_t,Ordering::Result>> t2_rel; // ∃x. x rel t2

  decltype(_nodes)::Iterator it(_nodes);
  while (it.hasNext()) {
    auto& e = it.next();
    auto comp1 = _ord.compare(t1,e.key());
    if (comp1 != Ordering::INCOMPARABLE) {
      t1_rel.push({ e.value(), comp1 });
    }
    auto comp2 = _ord.compare(e.key(),t2);
    if (comp2 != Ordering::INCOMPARABLE) {
      t2_rel.push({ e.value(), comp2 });
    }
  }
  for (const auto& [e1,r1] : t1_rel) {
    for (const auto& [e2,r2] : t2_rel) {
      auto r = e1 == e2 ? PoComp::EQUAL : _po->get(e1,e2);
      switch (r) {
        case PoComp::UNKNOWN:
          break;
        case PoComp::EQUAL: {
          switch (r1) {
            case Ordering::GREATER: {
              if (r2 != Ordering::LESS) {
                // t1 > e1 = e2 ≥ t2 -> t1 > t2
                ALWAYS(checkCompatibility(res, PoComp::GREATER, res));
              }
              break;
            }
            case Ordering::EQUAL: {
              // t1 = e1 = e2 r2 t2 -> t1 r2 t2
              ALWAYS(checkCompatibility(res, resultToPoComp(r2, false), res));
              break;
            }
            case Ordering::LESS: {
              if (r2 != Ordering::GREATER) {
                // t1 < e1 = e2 ≤ t2 -> t1 < t2
                ALWAYS(checkCompatibility(res, PoComp::LESS, res));
              }
              break;
            }
            case Ordering::INCOMPARABLE:
              ASSERTION_VIOLATION;
          }
          break;
        }
        case PoComp::GREATER:
        case PoComp::NLEQ: {
          if (r1 != Ordering::LESS && r2 != Ordering::LESS) {
            // t1 ≥ e1 > e2 ≥ t2 -> t1 > t2
            // t1 ≥ e1 ≰ e2 ≥ t2 -> t1 ≰ t2
            ALWAYS(checkCompatibility(res, r, res));
          }
          break;
        }
        case PoComp::LESS:
        case PoComp::NGEQ: {
          if (r1 != Ordering::GREATER && r2 != Ordering::GREATER) {
            // t1 ≤ e1 < e2 ≤ t2 -> t1 < t2
            // t1 ≤ e1 ≱ e2 ≤ t2 -> t1 ≱ t2
            ALWAYS(checkCompatibility(res, r, res));
          }
          break;
        }
        case PoComp::INCOMPARABLE: {
          if (r1 != Ordering::GREATER && r2 != Ordering::GREATER) {
            // t1 ≤ e1 ≱ e2 ≤ t2 -> t1 ≱ t2
            ALWAYS(checkCompatibility(res, PoComp::NGEQ, res));
          }
          if (r1 != Ordering::LESS && r2 != Ordering::LESS) {
            // t1 ≥ e1 ≰ e2 ≥ t2 -> t1 ≰ t2
            ALWAYS(checkCompatibility(res, PoComp::NLEQ, res));
          }
          break;
        }
      }
    }
  }
  return res;
}

bool TermPartialOrdering::set(TermOrderingConstraint con)
{
  size_t x = getIdExt(con.lhs);
  size_t y = getIdExt(con.rhs);

  bool reversed = x > y;
  if (reversed) {
    swap(x,y);
  }
  PoComp new_val = resultToPoComp(con.rel, reversed);
  _po = PartialOrdering::set(_po, x, y, new_val);
  if (!_po) {
    return false;
  }
#if DEBUG_ORDERING
  // debug_check();
#endif
  return true;
}

bool TermPartialOrdering::hasIncomp() const
{
  return _po->hasIncomp();
}

Result TermPartialOrdering::solveVarVar(POStruct* po_struct, AppliedTerm s, AppliedTerm t)
{
  ASS(po_struct);
  ASS(s.apply().isVar());
  ASS(t.apply().isVar());
  Result val = po_struct->tpo->get(s.term, t.term);
  if (val != Ordering::LESS && val != Ordering::INCOMPARABLE) {
    return val;
  }
  TermOrderingConstraint con{ s.term, t.term, Ordering::GREATER };
  auto etpo = TermPartialOrdering::set(po_struct->tpo, con);
  if (etpo && !etpo->hasIncomp()) {
    if (etpo != po_struct->tpo) {
      po_struct->tpo = etpo;
      po_struct->cons.push(con);
    }
    return Ordering::GREATER;
  }

  con.rel = Ordering::EQUAL;
  etpo = TermPartialOrdering::set(po_struct->tpo, con);
  if (etpo && !etpo->hasIncomp()) {
    if (etpo != po_struct->tpo) {
      po_struct->tpo = etpo;
      po_struct->cons.push(con);
    }
    return Ordering::EQUAL;
  }
  return Ordering::INCOMPARABLE;
}

Result TermPartialOrdering::solveTermVar(POStruct* po_struct, AppliedTerm s, AppliedTerm t)
{
  ASS(po_struct);
  ASS(s.apply().isTerm());
  ASS(t.apply().isVar());
  if (!s.aboveVar) {
    VariableIterator vit(s.term);
    while (vit.hasNext()) {
      auto v = vit.next();
      auto comp = solveVarVar(po_struct, v, t);
      if (comp != Ordering::INCOMPARABLE) {
        return comp;
      }
    }
    return Ordering::INCOMPARABLE;
  }
  ASS(s.term.isTerm());
  VariableIterator vit(s.term);
  while (vit.hasNext()) {
    auto vS = (*s.applicator)(vit.next().var());
    VariableIterator vitInner(vS);
    while (vitInner.hasNext()) {
      auto v = vitInner.next();
      auto comp = solveVarVar(po_struct, v, t);
      if (comp != Ordering::INCOMPARABLE) {
        // TODO we should probably return GREATER when comp==EQUAL
        return comp;
      }
    }
  }
  return Ordering::INCOMPARABLE;
}

size_t TermPartialOrdering::getId(TermList t) const
{
  ASS(_nodes.find(t));
  return _nodes.get(t);
}

size_t TermPartialOrdering::getIdExt(TermList t)
{
  size_t *ptr;
  if (_nodes.getValuePtr(t, ptr, _nodes.size())) {
    _po = PartialOrdering::extend(_po);

    // fill out new row with known values
    size_t idx = _nodes.size()-1;
    decltype(_nodes)::Iterator it(_nodes);
    while (it.hasNext()) {
      auto& e = it.next();
      if (e.value()==idx) {
        continue;
      }
      auto comp = _ord.compare(e.key(),t);
      if (comp == Ordering::INCOMPARABLE) {
        continue;
      }
      auto val = resultToPoComp(comp, false);
      _po = PartialOrdering::set(_po, e.value(), idx, val);
      ASS(_po);
    }
  }
  return *ptr;
}

ostream& operator<<(ostream& str, const TermPartialOrdering& tpo)
{
  typename Map<TermList,size_t>::Iterator it1(tpo._nodes);
  while (it1.hasNext()) {
    const auto& e1 = it1.next();
    typename Map<TermList,size_t>::Iterator it2(tpo._nodes);
    while (it2.hasNext()) {
      const auto& e2 = it2.next();
      if (e1.value() >= e2.value()) {
        continue;
      }
      auto pocomp = tpo._po->get(e1.value(),e2.value());
      if (pocomp == PoComp::UNKNOWN) {
        continue;
      }
      str << e1.key() << " " << pocompToInfix(pocomp) << " " << e2.key() << endl;
    }
  }
  return str;
}

#if DEBUG_ORDERING
void TermPartialOrdering::debug_check() const
{
  // auto output_args = [this](size_t x, size_t y, size_t z) {
  //   return _po->all_to_string() + " at " + Int::toString(x) + ", " + Int::toString(y) + ", " + Int::toString(z);
  // };

  auto check_val = [/* &output_args */](auto actual_val, auto expected_val, size_t x, size_t y, size_t z) {
    if (actual_val == PoComp::UNKNOWN) {
      // INVALID_OPERATION(output_args(x,y,z));
    }
    if (expected_val == PoComp::NLEQ) {
      if (actual_val != PoComp::NLEQ && actual_val != PoComp::INCOMPARABLE && actual_val != PoComp::GREATER) {
        // INVALID_OPERATION(output_args(x,y,z));
      }
    } else if (expected_val == PoComp::NGEQ) {
      if (actual_val != PoComp::NGEQ && actual_val != PoComp::INCOMPARABLE && actual_val != PoComp::LESS) {
        // INVALID_OPERATION(output_args(x,y,z));
      }
    } else {
      if (actual_val != expected_val) {
        // INVALID_OPERATION(output_args(x,y,z));
      }
    }
  };

  decltype(_nodes)::Iterator it1(_nodes);
  while (it1.hasNext()) {
    auto& e1 = it1.next();

    decltype(_nodes)::Iterator it2(_nodes);
    while (it2.hasNext()) {
      auto& e2 = it2.next();
      if (e1.value() == e2.value()) {
        continue;
      }
      auto v12 = _po->get(e1.value(),e2.value());
      if (v12 == PoComp::UNKNOWN) {
        continue;
      }
      auto comp = _ord.compare(e1.key(),e2.key());
      if (comp != Ordering::INCOMPARABLE) {
        check_val(v12, resultToPoComp(comp, false), e1.value(), e2.value(), e2.value());
      }

      decltype(_nodes)::Iterator it3(_nodes);
      while (it3.hasNext()) {
        auto& e3 = it3.next();
        if (e1.value() == e3.value() || e2.value() == e3.value()) {
          continue;
        }

        auto v13 = _po->get(e1.value(),e3.value());
        if (v13 == PoComp::UNKNOWN) {
          continue;
        }

        auto v23 = _po->get(e2.value(),e3.value());

        switch (v12) {
          case PoComp::UNKNOWN:
            break;
          case PoComp::EQUAL:
            // x = y rel z -> x rel z
            check_val(v13, v23, e1.value(), e2.value(), e3.value());
            break;
          case PoComp::GREATER:
          case PoComp::NLEQ: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::GREATER) {
              // x > y ≥ z -> x > z
              // x ≰ y ≥ z -> x ≰ z
              check_val(v13, v12, e1.value(), e2.value(), e3.value());
            }
            break;
          }
          case PoComp::LESS:
          case PoComp::NGEQ: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::LESS) {
              // x < y ≤ z -> x < z
              // x ≱ y ≤ z -> x ≱ z
              check_val(v13, v12, e1.value(), e2.value(), e3.value());
            }
            break;
          }
          case PoComp::INCOMPARABLE: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::GREATER) {
              // x ≰ y ≥ z -> x ≰ z
              check_val(v13, PoComp::NLEQ, e1.value(), e2.value(), e3.value());
            }
            if (v23 == PoComp::EQUAL || v23 == PoComp::LESS) {
              // x ≱ y ≤ z -> x ≱ z
              check_val(v13, PoComp::NGEQ, e1.value(), e2.value(), e3.value());
            }
            break;
          }
        }
      }
    }
  }
}
#endif

}