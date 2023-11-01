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
 * @file VarOrder.cpp
 */

#include "Forwards.hpp"
#include "Debug/TimeProfiling.hpp"

#include "VarOrder.hpp"

namespace Kernel {

using namespace std;

bool VarOrder::add_gt(unsigned x, unsigned y)
{
  return _po.set(x, y, PoComp::GT);
}

bool VarOrder::add_eq(unsigned x, unsigned y)
{
  return _po.set(x, y, PoComp::EQ);
}

PoComp VarOrder::query(unsigned x, unsigned y) const
{
  return _po.get(x, y);
}

bool VarOrder::is_total(size_t n) const
{
  return _po.size() == n && _po.is_total();
}

vstring VarOrder::to_string() const
{
  // return Int::toString(_po.size()) + ": " + _po.to_string() + ", " + _po.to_string_raw();
  return _po.to_string();
}

const List<Edge>* VarOrder::transitive_reduction() const
{
  return _po.transitive_reduction();
}

bool VarOrder::is_empty() const
{
  return _po.size() < 2;
}

TermList VarOrder::EqApplicator::apply(unsigned v)
{
  return TermList(_vo._po.get_rep(v),false);
}

VirtualIterator<std::tuple<unsigned,unsigned,PoComp>> VarOrder::iter_relations() const
{
  return _po.iter_relations();
}

size_t VarOrder::rel_size() const
{
  return _po.size();
}

bool VarOrder::subseteq(const VarOrder& other) const
{
  return _po.subseteq(other._po);
}

bool VarOrder::tryExtendWith(const VarOrder& other)
{
  auto rel = other.iter_relations();
  while (rel.hasNext()) {
    auto t = rel.next();
    unsigned x = get<0>(t);
    unsigned y = get<1>(t);
    PoComp v = get<2>(t);
    ASS(v!=PoComp::INC);
    if (v == PoComp::EQ) {
      if (!add_eq(x,y)) {
        return false;
      }
    } else if (v == PoComp::GT) {
      if (!add_gt(x,y)) {
        return false;
      }
    } else if (v == PoComp::LT) {
      if (!add_gt(y,x)) {
        return false;
      }
    }
  }
  return true;
}

}