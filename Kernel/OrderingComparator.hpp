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
 * @file OrderingComparator.hpp
 */

#ifndef __OrderingComparator__
#define __OrderingComparator__

#include "Forwards.hpp"

#include "Ordering.hpp"

namespace Kernel {

/**
 * Class implementing runtime specialized ordering check between two terms.
 * The comparator is created and called from inside the respective ordering
 * object, but owned by the caller, so the destructor is exposed as virtual.
 * See @b KBOComparator and @b LPOComparator for implementation details.
 */
struct OrderingComparator
{
  OrderingComparator(const Ordering& ord, TermList lhs, TermList rhs) : _ord(ord), _root(lhs, rhs) {}
  virtual ~OrderingComparator();
  virtual bool check(const SubstApplicator* applicator) { return false; }
  virtual void merge(const OrderingComparator& other);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

  enum class BranchTag : uint8_t {
    T_GREATER,
    T_NOT_GREATER,
    T_COMPARISON,
    T_WEIGHT,
    T_UNKNOWN,
  };

  struct Node;

  struct Branch {
    BranchTag tag;
    SmartPtr<Node> n;

    explicit Branch(BranchTag t) : tag(t) { ASS(t==BranchTag::T_GREATER || t==BranchTag::T_NOT_GREATER); }
    explicit Branch(TermList lhs, TermList rhs)
      : tag(BranchTag::T_UNKNOWN), n(new ComparisonNode(lhs, rhs)) {}
    explicit Branch(int w, Stack<std::pair<unsigned,int>>&& varCoeffPairs)
      : tag(BranchTag::T_WEIGHT), n(new WeightNode(w, std::move(varCoeffPairs))) {}
  };

  struct Node {
    Node() : eqBranch(BranchTag::T_NOT_GREATER), gtBranch(BranchTag::T_GREATER), incBranch(BranchTag::T_NOT_GREATER), ts(0) {}

    auto& getBranch(Ordering::Result r) {
      switch (r) {
        case Ordering::EQUAL:
          return eqBranch;
        case Ordering::GREATER:
          return gtBranch;
        case Ordering::INCOMPARABLE:
          return incBranch;
        default:
          ASSERTION_VIOLATION;
      }
    }

    void setTs(unsigned val) { ts = val; }
    unsigned getTs() const { return ts; }

    Branch eqBranch;
    Branch gtBranch;
    Branch incBranch;
    unsigned ts;
  };

  class ComparisonNode : public Node {
    ComparisonNode(TermList lhs, TermList rhs) : lhs(lhs), rhs(rhs) {}

    // only allow calling ctor from Branch
    friend struct Branch;

  public:
    TermList lhs;
    TermList rhs;
  };

  using VarCoeffPair = std::pair<unsigned,int>;
  using TermPairRes = std::tuple<TermList,TermList,Ordering::Result>;

  class WeightNode : public Node {
    WeightNode(int w, Stack<VarCoeffPair>&& varCoeffPairs)
      : w(w), varCoeffPairs(varCoeffPairs) {}

    // only allow calling ctor from Branch
    friend struct Branch;

  public:
    int w;
    Stack<VarCoeffPair> varCoeffPairs;
  };

  const Ordering& _ord;
  Branch _root;
};

} // namespace Kernel

#endif