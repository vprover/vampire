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

#include "TermPartialOrdering.hpp"

#include "Ordering.hpp"

namespace Kernel {

using OrderingConstraints = Stack<Ordering::Constraint>;

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
public:
  OrderingComparator(const Ordering& ord);
  virtual ~OrderingComparator();

  bool check(const SubstApplicator* applicator);
  void insert(const OrderingConstraints& comps);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);
  std::string to_dot() const;

  class Subsumption {
  public:
    Subsumption(OrderingComparator& subsumer, const Ordering& ord, const OrderingConstraints& comps, bool ground);
    bool check();

  private:
    bool checkLeaf();

    OrderingComparator& subsumer;
    OrderingComparatorUP subsumed;
    Stack<OrderingComparator::Branch*> path;
    bool ground;
  };

protected:
  void expand();
  virtual void expandTermCase();
  void processVarCase();
  void processPolyCase();

  enum BranchTag {
    T_RESULT = 0u,
    T_TERM = 1u,
    T_POLY = 2u,
  };

  struct Node;

  struct Branch {
    Node* node() const { return _node; }
    void setNode(Node* node) {
      if (node) {
        node->incRefCnt();
      }
      if (_node) {
        _node->decRefCnt();
      }
      _node = node;
    }

    Branch() = default;
    explicit Branch(bool result) {
      setNode(new Node(result));
      _node->ready = true;
    }
    template<typename S, typename T> Branch(S&& s, T&& t) {
      setNode(new Node(std::forward<S>(s), std::forward<T>(t)));
    }
    ~Branch();
    Branch(const Branch& other);
    Branch& operator=(const Branch& other);
    Branch(Branch&& other);
    Branch& operator=(Branch&& other);

  private:
    Node* _node = nullptr;
  };

  friend std::ostream& operator<<(std::ostream& out, const Node& node);
  friend std::ostream& operator<<(std::ostream& out, const BranchTag& t);

  using VarCoeffPair = std::pair<unsigned,int>;

  using Trace = TermPartialOrdering;

  ScopedPtr<Trace> getCurrentTrace();

  struct Node {
    static_assert(sizeof(uint64_t) == sizeof(Branch));
    static_assert(sizeof(uint64_t) == sizeof(TermList));
    static_assert(sizeof(uint64_t) == sizeof(void*));
    static_assert(sizeof(uint64_t) == sizeof(int64_t));

    auto& getBranch(Ordering::Result r) {
      switch (r) {
        case Ordering::GREATER:
          return gtBranch;
        case Ordering::EQUAL:
          return eqBranch;
        case Ordering::INCOMPARABLE:
          return ngeBranch;
        default:
          ASSERTION_VIOLATION;
      }
    }

    explicit Node(bool result)
      : tag(T_RESULT), result(result) {}
    explicit Node(TermList lhs, TermList rhs)
      : tag(T_TERM), lhs(lhs), rhs(rhs) {}
    explicit Node(uint64_t w, Stack<VarCoeffPair>* varCoeffPairs)
      : tag(T_POLY), w(w), varCoeffPairs(varCoeffPairs) {}
    Node(const Node&) = delete;
    Node& operator=(const Node&) = delete;

    ~Node();

    void incRefCnt();
    void decRefCnt();

    BranchTag tag;
    bool ready = false;

    union {
      bool result;
      TermList lhs;
      int64_t w;
    };
    union {
      TermList rhs;
      Stack<VarCoeffPair>* varCoeffPairs;
    };

    Branch gtBranch;
    Branch eqBranch;
    Branch ngeBranch;
    int refcnt = 0;
    Trace* trace = nullptr;
  };

  const Ordering& _ord;
  Branch _source;
  Branch _fail;
  Branch* _curr;
  Branch* _prev;
  // Trace _trace;
};

} // namespace Kernel

#endif