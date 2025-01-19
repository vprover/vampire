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

namespace Inferences {
  class ForwardGroundJoinability;
  class ForwardGroundReducibility;
}

namespace Shell {
  class ConditionalRedundancySubsumption;
  class ConditionalRedundancySubsumption2;
}

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
 * See @b KBOComparator and @b LPOComparator for implementation details.
 */
struct OrderingComparator
{
public:
  OrderingComparator(const Ordering& ord, bool onlyVars, bool ground, const TermPartialOrdering* head);
  virtual ~OrderingComparator();

  /** Has to be called each time a new retrieval is started. */
  void init(const SubstApplicator* appl);

  /** After calling @b init, repeated calls to @b next results in all
   *  user-defined (non-null) data that has true corresponding ordering
   *  constraints, or in null when no further such data can be retreived. */
  void* next(POStruct* po_struct = nullptr);

  /** Inserts a conjunctions of term ordering constraints and user-allocated data. */
  void insert(const Stack<TermOrderingConstraint>& cons, void* data);

  bool checkAndCompress();

  bool extractVarOrder(const SubstApplicator* appl, POStruct& po_struct);

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

private:
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
   *  See @b KBOComparator and @b LPOComparator. */
  virtual void processTermNode();

  /** As noted above, a processed node can be reached via exactly one path,
   *  and we use this to get a conjunction of term ordering constraints on
   *  this path which is then used to simplify the node. The trace contains
   *  these constraints. */
  using Trace = TermPartialOrdering;
  const Trace* getCurrentTrace();

  struct Node;
  struct Polynomial;

  std::pair<Node*, Result> getPrevPoly();

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

    Branch eqBranch;
    Branch gtBranch;
    Branch ngeBranch;
    bool ready = false;
    int refcnt = 0;
    const Trace* trace = nullptr;
    // points to the previous node containing a polynomial and branch
    // that was taken, otherwise null if no such node exists.
    std::pair<Node*, Result> prevPoly = { nullptr, Result::INCOMPARABLE };
  };

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

  friend class Inferences::ForwardGroundJoinability;
  friend class Inferences::ForwardGroundReducibility;
  friend class Shell::ConditionalRedundancySubsumption;
  friend class Shell::ConditionalRedundancySubsumption2;

  const Ordering& _ord;
  Branch _source;
  Branch _sink;
  Branch* _curr;
  Branch* _prev;
  const SubstApplicator* _appl;
  bool _onlyVars;
  bool _ground;
  const TermPartialOrdering* _head;

public:
  struct VarOrderExtractor {
    void init(OrderingComparatorUP comp);

    bool extract(POStruct& po_struct);
    bool tryExtend(POStruct& po_struct, const Stack<TermOrderingConstraint>& cons);

    OrderingComparatorUP _comp;

    struct BranchingPoint {
      Stack<TermOrderingConstraint> cons;
      Branch* branch;
    };
    void initCurrent(Stack<BranchingPoint>* ptr);

    DHMap<Branch*, Stack<BranchingPoint>> _map;
  };

  struct VarOrderExtractor2 {
    VarOrderExtractor2(const Ordering& ord, TermList lhs, TermList rhs, const SubstApplicator* appl, POStruct po_struct);

    // bool hasAlternative() { _path.isNonEmpty(); }
    std::pair<Result,POStruct> next();

    bool tryExtend(POStruct& po_struct, const Stack<TermOrderingConstraint>& cons);

    OrderingComparatorUP _comp;

    struct BranchingPoint {
      Stack<TermOrderingConstraint> cons;
      Branch* branch;
    };
    void initCurrent(Stack<BranchingPoint>* ptr);

    DHMap<Branch*, Stack<BranchingPoint>> _map;
    Stack<std::tuple<Branch*,POStruct,unsigned>> _path;
    POStruct _po_struct;
  };
};

} // namespace Kernel

#endif