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
protected:
  struct Branch;
  struct Node;
  class ResultNode;
  class ComparisonNode;

public:
  OrderingComparator(const Ordering& ord, const Stack<Ordering::Constraint>& comps, void* result);
  virtual ~OrderingComparator();

  void reset() { _curr = &_root; _cache.reset(); }
  bool check(const SubstApplicator* applicator) {
    reset();
    return next(applicator)!=nullptr;
  }
  const Stack<Ordering::Constraint>& cache() const { return _cache; }

  void* next(const SubstApplicator* applicator);
  void addAlternative(const OrderingComparator& other);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

protected:
  virtual void expand();
  bool tryExpandVarCase(ComparisonNode* origNode);

  enum class BranchTag : uint8_t {
    T_RESULT,
    T_COMPARISON,
    T_WEIGHT,
  };

  struct Branch {
    BranchTag tag;
    SmartPtr<Node> n;
    bool ready = false;

    Branch() : tag(BranchTag::T_RESULT), ready(true) {}
    explicit Branch(void* data) : tag(BranchTag::T_RESULT), n(new ResultNode(data)) {}
    explicit Branch(TermList lhs, TermList rhs)
      : tag(BranchTag::T_COMPARISON), n(new ComparisonNode(lhs, rhs)) {}
    explicit Branch(int w, Stack<std::pair<unsigned,int>>&& varCoeffPairs)
      : tag(BranchTag::T_WEIGHT), n(new WeightNode(w, std::move(varCoeffPairs))), ready(true) {}
  };

  friend std::ostream& operator<<(std::ostream& out, const Branch& branch);
  friend std::ostream& operator<<(std::ostream& out, const BranchTag& t);

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

  class ResultNode : public Node {
    ResultNode(void* data) : data(data) {}

    // only allow calling ctor from Branch
    friend struct Branch;
  
  public:
    void* data;
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
  Stack<Ordering::Constraint> _cache;
};

} // namespace Kernel

#endif