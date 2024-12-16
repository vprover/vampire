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
  OrderingComparator(const Ordering& ord, bool onlyVars);
  virtual ~OrderingComparator();

  void reset() { _curr = &_source; _prev = nullptr; /* _trace.reset(); */ }

  void* next(const SubstApplicator* applicator);
  void insert(const Stack<Ordering::Constraint>& comps, void* result);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);
  std::string to_dot() const;

  class Subsumption {
  public:
    Subsumption(OrderingComparator& subsumer, const Ordering& ord, const OrderingConstraints& comps, bool ground);
    bool check();

  private:
    void pushNext();

    OrderingComparator& subsumer;
    OrderingComparatorUP subsumed;
    Stack<std::tuple<Branch*,Branch*,Branch*>> path;
    bool ground;
  };

  class RedundancyCheck {
  public:
    RedundancyCheck(const Ordering& ord, void* data);
    std::pair<void*,const TermPartialOrdering*> next(OrderingConstraints cons, void* data);

  private:
    void pushNext();

    OrderingComparatorUP comp;
    Stack<Branch*> path;
  };

protected:
  void expand();
  virtual void expandTermCase();
  void processVarCase();
  void processPolyCase();

  enum BranchTag {
    T_DATA = 0u,
    T_TERM = 1u,
    T_POLY = 2u,
  };

  struct Node;
  struct Polynomial;

  struct LinearConstraint {
    const Polynomial* poly;
    enum class Sign {
      EQ,
      GEQ,
      GT,
    } sign;
  };
  using LinearConstraints = Stack<LinearConstraint>;
  using LCSign = LinearConstraint::Sign;

  bool fourierMotzkin(LinearConstraints linCons);

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
    template<typename S, typename T> Branch(S&& s, T&& t) {
      setNode(new Node(std::forward<S>(s), std::forward<T>(t)));
    }
    Branch(const Polynomial* p) {
      setNode(new Node(p));
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
  friend std::ostream& operator<<(std::ostream& out, const Polynomial& poly);
  friend std::ostream& operator<<(std::ostream& str, const LCSign& lcSign);
  friend std::ostream& operator<<(std::ostream& str, const LinearConstraint& linCon);

  using VarCoeffPair = std::pair<unsigned,int>;

  struct Polynomial {
    static const Polynomial* get(int constant, const Stack<VarCoeffPair>& varCoeffPairs);

    auto asTuple() const { return std::make_tuple(constant, varCoeffPairs); }

    // return -P where P is the current polynomial
    const Polynomial* negate() const;
    // returns c ⋅ P + d ⋅ Q where P is the current polynomial
    const Polynomial* add(int c, const Polynomial* Q, int d) const;

    IMPL_HASH_FROM_TUPLE(Polynomial);
    IMPL_COMPARISONS_FROM_TUPLE(Polynomial);

    int constant;
    // variable-coefficient pairs sorted by sign
    // (positive first), and then by variable
    // e.g. X1 + 2 ⋅ X4 - 5 ⋅ X0 - X3
    Stack<VarCoeffPair> varCoeffPairs;
  };

  using Trace = TermPartialOrdering;

  const Trace* getCurrentTrace();
  std::pair<Node*, Result> getPrevPoly();

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
          return ngeBranch;
        default:
          ASSERTION_VIOLATION;
      }
    }

    explicit Node(void* data, Branch alternative)
      : tag(T_DATA), data(data), alternative(alternative) {}
    explicit Node(TermList lhs, TermList rhs)
      : tag(T_TERM), lhs(lhs), rhs(rhs) {}
    explicit Node(const Polynomial* p)
      : tag(T_POLY), poly(p) {}
    Node(const Node&) = delete;
    Node& operator=(const Node&) = delete;

    ~Node();

    void incRefCnt();
    void decRefCnt();

    BranchTag tag;
    bool ready = false;

    union {
      void* data = nullptr;
      TermList lhs;
      const Polynomial* poly;
    };
    union {
      Branch alternative;
      TermList rhs;
    };

    Branch eqBranch;
    Branch gtBranch;
    Branch ngeBranch;
    int refcnt = 0;
    const Trace* trace = nullptr;
    // points to the previous node containing a polynomial and branch
    // that was taken, otherwise null if no such node exists.
    std::pair<Node*, Result> prevPoly = { nullptr, Result::INCOMPARABLE };
  };

  const Ordering& _ord;
  Branch _source;
  Branch _sink;
  Branch* _curr;
  Branch* _prev;
  // Trace _trace;
  bool _onlyVars;
};

} // namespace Kernel

#endif