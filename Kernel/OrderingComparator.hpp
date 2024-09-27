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

  void* next(const SubstApplicator* applicator);
  void addAlternative(const OrderingComparator& other);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

protected:
  void expand();
  virtual void expandTermCase();
  bool tryExpandVarCase();

  enum BranchTag {
    T_RESULT = 0u,
    T_COMPARISON = 1u,
    T_WEIGHT = 2u,
  };

  struct Branch {
    static_assert(alignof(Node*)>T_WEIGHT);
    static constexpr unsigned
      READY_BITS_START = 0,
      READY_BITS_END = READY_BITS_START + 1,
      TAG_BITS_START = READY_BITS_END,
      TAG_BITS_END = TAG_BITS_START + 2,
      NODE_BITS_START = TAG_BITS_END,
      NODE_BITS_END = CHAR_BIT * sizeof(Node*);

    BITFIELD64_GET_AND_SET(bool, ready, Ready, READY)
    BITFIELD64_GET_AND_SET(unsigned, tag, Tag, TAG)
    // BITFIELD64_GET_AND_SET_PTR(Node*, node, Node, NODE)
    Node* _node() const { return reinterpret_cast<Node*>(BitUtils::getBits<NODE_BITS_START,NODE_BITS_END>(_content)); }
    void _setNode(Node* node) {
      auto prev = _node();
      if (prev) {
        prev->decRefCnt();
      }
      if (node) {
        node->incRefCnt();
      }
      BitUtils::setBits<NODE_BITS_START,NODE_BITS_END>(_content, reinterpret_cast<uint64_t>(node));
    }

    Branch() { _setTag(T_RESULT); _setReady(true); _setNode(nullptr); }
    explicit Branch(void* data, Branch alternative) {
      _setTag(T_RESULT);
      _setNode(new Node(data, alternative));
    }
    explicit Branch(TermList lhs, TermList rhs) {
      _setTag(T_COMPARISON);
      _setNode(new Node(lhs, rhs));
    }
    explicit Branch(int64_t w, Stack<std::pair<unsigned,int>>* varCoeffPairs) {
      _setTag(T_WEIGHT);
      _setNode(new Node(w, varCoeffPairs));
      _setReady(true);
    }
    // Branch(const Branch& other) = delete;
    // Branch& operator=(const Branch& other) = delete;
    Branch(const Branch& other) {
      _setTag(other._tag());
      _setReady(other._ready());
      _setNode(other._node());
    }
    Branch& operator=(const Branch& other) {
      if (&other==this) {
        return *this;
      }
      _setTag(other._tag());
      _setReady(other._ready());
      _setNode(other._node());
      return *this;
    }
    Branch(Branch&& other) : _content(other._content) {
      other._content = 0;
    }
    Branch& operator=(Branch&& other) {
      if (&other==this) {
        return *this;
      }
      _content = other._content;
      other._content = 0;
      return *this;
    }

  private:
    uint64_t _content = 0;
  };

  friend std::ostream& operator<<(std::ostream& out, const Branch& branch);
  friend std::ostream& operator<<(std::ostream& out, const BranchTag& t);

  using VarCoeffPair = std::pair<unsigned,int>;

  struct Node {
    static_assert(sizeof(uint64_t) == sizeof(Branch));
    static_assert(sizeof(uint64_t) == sizeof(TermList));
    static_assert(sizeof(uint64_t) == sizeof(void*));
    static_assert(sizeof(uint64_t) == sizeof(int64_t));

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

    explicit Node(void* data, Branch alternative)
      : data(data), alternative(alternative) {}
    explicit Node(TermList lhs, TermList rhs)
      : lhs(lhs), rhs(rhs) {}
    explicit Node(uint64_t w, Stack<VarCoeffPair>* varCoeffPairs)
      : w(w), varCoeffPairs(varCoeffPairs) {}

    void incRefCnt();
    void decRefCnt();

    union {
      void* data = nullptr;
      TermList lhs;
      int64_t w;
    };
    union {
      Branch alternative;
      TermList rhs;
      Stack<VarCoeffPair>* varCoeffPairs;
    };

    Branch eqBranch;
    Branch gtBranch;
    Branch incBranch;
    unsigned ts;
    unsigned refcnt;
  };

  const Ordering& _ord;
  Branch _root;
  Branch* _curr;
  Stack<Ordering::Constraint> _cache;
};

} // namespace Kernel

#endif