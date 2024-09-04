/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __LPOComparator__
#define __LPOComparator__

#include "Forwards.hpp"

#include "LPO.hpp"

namespace Kernel {

using namespace Lib;
using namespace std;

class LPOComparator
: public OrderingComparator
{
public:
  LPOComparator(TermList lhs, TermList rhs, const LPO& lpo);

  /** Executes the runtime specialized instructions with concrete substitution. */
  bool check(const SubstApplicator* applicator) override;
  std::string toString() const override;

  /* A branch initially has a T_UNKNOWN tag, and after first processing becomes either
   * a specific result T_GREATER/T_NOT_GREATER or a pointer to a comparison node. */
  enum class BranchTag : uint8_t {
    T_GREATER,
    T_NOT_GREATER,
    T_COMPARISON,
    T_UNKNOWN,
  };

  struct Node;

  struct Branch {
    BranchTag tag;
    Node* n;

    explicit Branch(BranchTag t) : tag(t), n(nullptr) { ASS(t==BranchTag::T_GREATER || t==BranchTag::T_NOT_GREATER); }
    explicit Branch(Node* n) : tag(BranchTag::T_UNKNOWN), n(n) { ASS(n); n->acquire(); }
    Branch(const Branch& other) : tag(other.tag), n(other.n) { if (n) { n->acquire(); } }
    ~Branch() { if (n) { n->release(); } }
    Branch& operator=(const Branch& other) {
      if (this != &other) {
        tag = other.tag;
        if (n) { n->release(); }
        n = other.n;
        if (n) { n->acquire(); }
      }
      return *this;
    }
  };

  struct Node {
    Node(TermList lhs, TermList rhs)
      : refcnt(0), lhs(lhs), rhs(rhs), eqBranch(BranchTag::T_NOT_GREATER), gtBranch(BranchTag::T_GREATER), incBranch(BranchTag::T_NOT_GREATER) {}

    void acquire() {
      refcnt++;
    }

    void release() {
      ASS(refcnt);
      refcnt--;
      if (!refcnt) {
        delete this;
      }
    }

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

    unsigned refcnt;
    TermList lhs;
    TermList rhs;
    Branch eqBranch;
    Branch gtBranch;
    Branch incBranch;
  };

private:
  static void majoChain(Branch* branch, TermList tl1, Term* t, unsigned i, Branch success, Branch fail);
  static void alphaChain(Branch* branch, Term* s, unsigned i, TermList tl2, Branch success, Branch fail);
  static void expand(Branch& branch, const LPO& lpo);

  friend ostream& operator<<(ostream& str, const LPOComparator& comp);

  Branch _root;
};

}
#endif
