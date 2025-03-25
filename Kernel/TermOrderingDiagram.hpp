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
 * @file TermOrderingDiagram.hpp
 */

#ifndef __TermOrderingDiagram__
#define __TermOrderingDiagram__

#include "Forwards.hpp"

#include "TermPartialOrdering.hpp"

#include "Ordering.hpp"

namespace Kernel {

/**
 * Class implementing term ordering diagrams which handle the following
 * problem. Given pairs (C_1,d_1),...,(C_n,d_n) where C_i are conjunctions
 * of ordering constraints and d_i are arbitrary data, and a substitution θ,
 * we want to retrieve all d_i s.t. C_iθ is true efficiently.
 *
 * TODO: refer to paper after publishing.
 *
 * The diagrams are created and called from inside a specific ordering
 * object (KBO or LPO), but owned by the caller, so the destructor is virtual.
 * See @b TermOrderingDiagramKBO and @b TermOrderingDiagramLPO for implementation details.
 */
struct TermOrderingDiagram
{
public:
  struct Node;
  using PrevPoly = std::pair<Node*,Ordering::Result>;

  static TermOrderingDiagram* createForSingleComparison(const Ordering& ord, TermList lhs, TermList rhs);

  TermOrderingDiagram(const Ordering& ord);
  virtual ~TermOrderingDiagram();

  /** Has to be called each time a new retrieval is started. */
  void init(const SubstApplicator* appl);

  /** After calling @b init, repeated calls to @b next results in all
   *  user-defined (non-null) data that has true corresponding ordering
   *  constraints, or in null when no further such data can be retreived. */
  void* next();

  bool check(const SubstApplicator* appl, const PrevPoly& prevPoly, const TermPartialOrdering* tpo);

  /** Inserts a conjunctions of term ordering constraints and user-allocated data. */
  void insert(const Stack<TermOrderingConstraint>& cons, void* data);

  friend std::ostream& operator<<(std::ostream& out, const TermOrderingDiagram& tod);

private:
  Result positivityCheck() const;

  /** Processes current node until it is either (i) a term or poly node whose result
   *  cannot be inferred from earlier comparisons, or (ii) a data node.
   *  We maintain the invariant that the subgraph containing only processed nodes
   *  in the diagram is a tree, so that each node can be reached via exactly one path. */
  void processCurrentNode();
  void processVarNode();
  void processPolyNode();

protected:
  /** Implements one step of a definitional expansion
   *  for two terms in a specific term ordering.
   *  See @b TermOrderingDiagramKBO and @b TermOrderingDiagramLPO. */
  virtual void processTermNode();

  /** As noted above, a processed node can be reached via exactly one path,
   *  and we use this to get a conjunction of term ordering constraints on
   *  this path which is then used to simplify the node. The trace contains
   *  these constraints. */
  using Trace = TermPartialOrdering;
  const Trace* getCurrentTrace();

  struct Polynomial;

  PrevPoly getPrevPoly();

  /** A branch is essentially a shared pointer for a node,
   *  except the node takes care of its own lifecycle. */
  struct Branch {
    Branch() = default;
    Branch(void* data, Branch alt);
    Branch(TermList lhs, TermList rhs);
    Branch(const Polynomial* p);

    ~Branch();

    Branch(const Branch& other);
    Branch(Branch&& other);
    Branch& operator=(Branch other);

    Node* node() const;
    void setNode(Node* node);

  private:
    Node* _node = nullptr;
  };

public:
  /** A node is a structure that either
   * (i)   contains user-defined data, or
   * (ii)  represents a term comparison, or
   * (iii) represents a polynomial zero check.
   */
  struct Node {
    enum Tag {
      T_DATA = 0u,
      T_TERM = 1u,
      T_POLY = 2u,
    } tag;

    explicit Node(void* data, Branch alternative);
    explicit Node(TermList lhs, TermList rhs);
    explicit Node(const Polynomial* p);

    ~Node();

    Node(const Node&) = delete;
    Node& operator=(const Node&) = delete;

    void incRefCnt();
    void decRefCnt();

    Branch& getBranch(Ordering::Result r);
    Branch& getBranchUnsafe(Ordering::Result r);

    // We need all this data to be of the same size
    static_assert(sizeof(uint64_t) == sizeof(Branch));
    static_assert(sizeof(uint64_t) == sizeof(TermList));
    static_assert(sizeof(uint64_t) == sizeof(void*));
    static_assert(sizeof(uint64_t) == sizeof(int64_t));

    // Tag specific data
    union {
      void* data = nullptr;
      TermList lhs;
      const Polynomial* poly;
    };
    union {
      Branch alternative;
      TermList rhs;
    };

    friend struct TermOrderingDiagram;
    friend class TermOrderingDiagramKBO;
    friend class TermOrderingDiagramLPO;
    friend std::ostream& operator<<(std::ostream&, const TermOrderingDiagram&);

  private:
    Branch eqBranch;
    Branch gtBranch;
    Branch ngeBranch;
  public:
    bool ready = false;
    int refcnt = 0;
    const Trace* trace = nullptr;
    // points to the previous node containing a polynomial and branch
    // that was taken, otherwise null if no such node exists.
    PrevPoly prevPoly = { nullptr, Result::INCOMPARABLE };
  };
protected:

  using VarCoeffPair = std::pair<unsigned,int>;

  struct Polynomial {
    static const Polynomial* get(int constant, const Stack<VarCoeffPair>& varCoeffPairs);

    auto asTuple() const { return std::make_tuple(constant, varCoeffPairs); }

    IMPL_HASH_FROM_TUPLE(Polynomial);
    IMPL_COMPARISONS_FROM_TUPLE(Polynomial);

    int constant;
    // variable-coefficient pairs sorted by sign
    // (positive first), and then by variable
    // e.g. X1 + 2 ⋅ X4 - 5 ⋅ X0 - X3
    Stack<VarCoeffPair> varCoeffPairs;
  };

  friend std::ostream& operator<<(std::ostream& out, const Node::Tag& t);
  friend std::ostream& operator<<(std::ostream& out, const Node& node);
  friend std::ostream& operator<<(std::ostream& out, const Polynomial& poly);

  const Ordering& _ord;
  Branch _source;
  Branch _sink;
  Branch* _curr;
  Branch* _prev;
  const SubstApplicator* _appl;
  bool _threeValued = false;

  struct TermNodeIterator {
    TermNodeIterator(const Ordering& ord, const SubstApplicator* appl,
      TermList lhs, TermList rhs, const PrevPoly& prevPoly, const TermPartialOrdering* tpo);

    Result get();

    const Ordering& _ord;
    TermOrderingDiagram* _tod;
    const PrevPoly& _prevPoly;
    const TermPartialOrdering* _tpo;
  };

  struct PolyNodeIterator {
    PolyNodeIterator(const Polynomial* poly, const PrevPoly& prevPoly, const TermPartialOrdering* tpo);

    Result get();

    const Polynomial* _poly;
    const PrevPoly& _prevPoly;
    const TermPartialOrdering* _tpo;
  };

public:
  struct GreaterIterator {
    GreaterIterator(const Ordering& ord, TermList lhs, TermList rhs);

    bool hasNext();
    std::pair<PrevPoly, const TermPartialOrdering*> next() { return _res; }

    TermOrderingDiagram& _tod;
    std::pair<PrevPoly, const TermPartialOrdering*> _res;
    Stack<Branch*> _path;
  };
};

} // namespace Kernel

#endif