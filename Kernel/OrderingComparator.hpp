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
  template<bool contrapositive> class ConditionalRedundancySubsumption3;
}

namespace Kernel {

class KBOComparator;
class LPOComparator;

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
  static OrderingComparator* createForSingleComparison(const Ordering& ord, TermList lhs, TermList rhs, bool ground);

  OrderingComparator(const Ordering& ord, bool onlyVars, bool ground, const TermPartialOrdering* head);
  virtual ~OrderingComparator();

  /** Has to be called each time a new retrieval is started. */
  void init(const SubstApplicator* appl);

  /** After calling @b init, repeated calls to @b next results in all
   *  user-defined (non-null) data that has true corresponding ordering
   *  constraints, or in null when no further such data can be retreived. */
  void* next();

  /** Inserts a conjunctions of term ordering constraints and user-allocated data. */
  void insert(const Stack<TermOrderingConstraint>& cons, void* data);

  bool checkAndCompress();

  friend std::ostream& operator<<(std::ostream& out, const OrderingComparator& comp);

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

    friend struct OrderingComparator;
    friend class KBOComparator;
    friend class LPOComparator;
    friend std::ostream& operator<<(std::ostream&, const OrderingComparator&);

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
  template<bool contrapositive> friend class Shell::ConditionalRedundancySubsumption3;

  const Ordering& _ord;
  Branch _source;
  Branch _sink;
  Branch* _curr;
  Branch* _prev;
  const SubstApplicator* _appl;
  bool _onlyVars;
  bool _ground;
  bool _threeValued = false;
  const TermPartialOrdering* _head;

public:
  struct VarOrderExtractor {
    VarOrderExtractor(OrderingComparator* comp, const SubstApplicator* appl, POStruct po_struct);

    bool hasNext(bool& nodebug);
    POStruct next() { return res; }

    struct Iterator {
      Iterator(const Ordering& ord, TermList lhs, TermList rhs, POStruct po_struct);

      std::pair<Result,POStruct> next();

      bool tryExtend(POStruct& po_struct, const Stack<TermOrderingConstraint>& cons);

      OrderingComparator* _comp;

      struct BranchingPoint {
        Stack<TermOrderingConstraint> cons;
        Branch* branch;
      };
      void initCurrent(Stack<BranchingPoint>* ptr);

      Map<Branch*, Stack<BranchingPoint>> _map;
      Recycled<Stack<std::tuple<Branch*,POStruct,unsigned>>> _path;
      POStruct _po_struct;
      bool _retIncomp = false;
    };

    bool backtrack();

    OrderingComparator* comp;
    const SubstApplicator* appl;
    Recycled<Stack<std::tuple<Branch*,POStruct,std::unique_ptr<Iterator>>>> path;
    Stack<unsigned> btStack;
    POStruct res;
    bool fresh = true;
  };

  struct Iterator {
    Iterator(const Ordering& ord, const TermPartialOrdering* trace, TermList lhs, TermList rhs);

    bool hasNext();
    std::pair<Result,const TermPartialOrdering*> next() { return res; }

    enum Res { GT = 0x1, EQ = 0x2, LT = 0x3, };

    OrderingComparator* comp;
    Stack<std::tuple<Branch*,Branch*,const TermPartialOrdering*,bool>> todo;
    std::pair<Result,const TermPartialOrdering*> res;
  };

  struct SomeIterator {
    SomeIterator(OrderingComparator& comp, const SubstApplicator* appl, const TermPartialOrdering* tpo)
      : _comp(comp), _appl(appl), _tpo(tpo) {}

    bool check(bool& backtracked);

    OrderingComparator& _comp;
    const SubstApplicator* _appl;
    const TermPartialOrdering* _tpo;
    Recycled<Stack<Branch*>> _btStack;
  };

  struct Iterator2 {
    Iterator2(const Ordering& ord, TermList lhs, TermList rhs, const TermPartialOrdering* tpo);

    Result get();

    enum Res { GT = 0x1, EQ = 0x2, LT = 0x3, };

    OrderingComparator* _comp;
    const TermPartialOrdering* _tpo;
  };

  struct PolyIterator {
    PolyIterator(const Ordering& ord, const Polynomial* poly, const TermPartialOrdering* tpo);

    Result get();

    const Polynomial* _poly;
    const TermPartialOrdering* _tpo;
  };

  struct GreaterIterator {
    GreaterIterator(const Ordering& ord, TermList lhs, TermList rhs);

    bool hasNext();
    const TermPartialOrdering* next() { return _tpo; }

    OrderingComparator& _comp;
    const TermPartialOrdering* _tpo;
    Stack<Branch*> _path;
  };
};

} // namespace Kernel

#endif