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
 * @file TermPartialOrdering.hpp
 * Defines class TermPartialOrdering.
 */

#ifndef __TermPartialOrdering__
#define __TermPartialOrdering__

#include "Forwards.hpp"

#include "Ordering.hpp"
#include "PartialOrdering.hpp"

namespace Kernel {

using namespace Lib;
using Result = Ordering::Result;

/** 
 * Class for ordering constraints capturing expressions
 * s ≻ t, s = t, s ≺ t or s ⋈ t for some terms s and t.
 */
struct TermOrderingConstraint {
  TermList lhs;
  TermList rhs;
  Result rel;

  friend std::ostream& operator<<(std::ostream& out, const TermOrderingConstraint& con)
  { return out << con.lhs << " " << con.rhs << " " << con.rel; }
};

/**
 * Class that represents a partial ordering between terms.
 * Uses @b PartialOrdering and is built similarly to increase
 * sharing.
 * 
 * Note that the structure is not complete as it is an under-
 * approximation of the actual relation. For example, given
 * x = f(y,z) and y = z, we should conclude x = f(z,y) but
 * this is in general hard to calculate so we fail.
 */
class TermPartialOrdering
{
public:
  /** Gets relation between two terms. If they are related, returns true
   *  and set the relation in @b res. Otherwise returns false. */
  bool get(TermList lhs, TermList rhs, Result& res) const;
  bool isGround() const { return _po->isGround(); }

  /** Get empty relation. */
  static const TermPartialOrdering* getEmpty(const Ordering& ord);
  /** Set relation between two terms given by a term ordering constraint. */
  static const TermPartialOrdering* set(const TermPartialOrdering* tpo, TermOrderingConstraint con);

  friend std::ostream& operator<<(std::ostream& str, const TermPartialOrdering& tpo);

private:
  TermPartialOrdering(const Ordering& ord) : _ord(ord), _po(PartialOrdering::getEmpty()) {}
  ~TermPartialOrdering() = default;

  bool set(TermOrderingConstraint con);

  PoComp getOneExternal(TermList t, size_t idx) const;
  PoComp getTwoExternal(TermList t1, TermList t2) const;

  size_t getId(TermList t) const;
  size_t getIdExt(TermList t);

  const Ordering& _ord;
  Map<TermList,size_t> _nodes;
  const PartialOrdering* _po;
};

};

#endif /* __PartialOrdering__ */