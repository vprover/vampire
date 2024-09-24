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
  struct Branch;
  struct Node;
  struct ResultNode;
  class ComparisonNode;

  OrderingComparator(const Ordering& ord, void* root) : _ord(ord),
    _root(*static_cast<Branch*>(root)), _curr(&_root), _cache() {}
  virtual ~OrderingComparator();

  void reset() { _curr = &_root; _cache.reset(); }
  bool check(const SubstApplicator* applicator) {
    reset();
    return next(applicator)!=nullptr;
  }

  ResultNode* next(const SubstApplicator* applicator);
  void addAlternative(const Branch& branch);

  using TermPairRes = std::tuple<TermList,TermList,Ordering::Result>;

  virtual void expand();
  bool tryExpandVarCase(ComparisonNode* origNode);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

  enum class BranchTag : uint8_t {
    T_RESULT,
    T_COMPARISON,
    T_WEIGHT,
    T_UNKNOWN,
  };

  struct Branch {
    BranchTag tag;
    SmartPtr<Node> n;

    Branch() : tag(BranchTag::T_RESULT) {}
    explicit Branch(ResultNode* r) : tag(BranchTag::T_RESULT), n(r) {}
    explicit Branch(TermList lhs, TermList rhs)
      : tag(BranchTag::T_UNKNOWN), n(new ComparisonNode(lhs, rhs)) {}
    explicit Branch(int w, Stack<std::pair<unsigned,int>>&& varCoeffPairs)
      : tag(BranchTag::T_WEIGHT), n(new WeightNode(w, std::move(varCoeffPairs))) {}
  };

  friend std::ostream& operator<<(std::ostream& out, const Branch& branch);

  struct Node {
    virtual ~Node() = default;

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

  struct ResultNode : public Node {
    Branch alternative;
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
  Branch* _curr;
  Stack<TermPairRes> _cache;
};

} // namespace Kernel

#endif