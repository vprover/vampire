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
  LPOComparator(const LPO& lpo) : _lpo(lpo), _instructions(), _res(Node::BranchTag::T_JUMP) {}
  static LPOComparator* create(TermList tl1, TermList tl2, const LPO& lpo);

  bool operator()(const SubstApplicator* applicator) const override;
  friend std::ostream& operator<<(std::ostream& out, const LPOComparator& comparator);

// private:
  struct Node {
    enum class BranchTag : uint8_t {
      T_EQUAL,
      T_GREATER,
      T_INCOMPARABLE,
      T_JUMP,
    };

    struct Branch {
      BranchTag tag;
      uint16_t jump_pos;
      bool operator==(const Branch& other) const {
        return std::tie(tag, jump_pos) == std::tie(other.tag, other.jump_pos);
      }
      bool operator<(const Branch& other) const {
        return std::tie(tag, jump_pos) < std::tie(other.tag, other.jump_pos);
      }
      static constexpr Branch eq() { return Branch{ BranchTag::T_EQUAL, 0 }; }
      static constexpr Branch gt() { return Branch{ BranchTag::T_GREATER, 0 }; }
      static constexpr Branch inc() { return Branch{ BranchTag::T_INCOMPARABLE, 0 }; }
      static constexpr Branch jump(uint16_t pos) { return Branch{ BranchTag::T_JUMP, pos }; }
    };

    Node(TermList lhs, TermList rhs)
      : lhs(lhs), rhs(rhs), bs() { bs[0] = Branch::eq(); bs[1] = Branch::gt(); bs[2] = Branch::inc(); }

    constexpr const auto& getBranch(Ordering::Result r) const {
      switch (r) {
        case Ordering::EQUAL:
          return bs[0];
        case Ordering::GREATER:
          return bs[1];
        case Ordering::INCOMPARABLE:
          return bs[2];
        default:
          ASSERTION_VIOLATION;
      }
    }

    bool operator<(const Node& other) const {
      return std::tie(lhs, rhs, bs[0], bs[1], bs[2]) <
        std::tie(other.lhs, other.rhs, other.bs[0], other.bs[1], other.bs[2]);
    }

    TermList lhs;
    TermList rhs;
    Branch bs[3];

    friend ostream& operator<<(ostream& out, const Node& n);
    friend ostream& operator<<(ostream& out, const Branch& b);
    friend ostream& operator<<(ostream& out, const BranchTag& bt);
  };

  static pair<Stack<Node>,Node::BranchTag> createHelper(TermList tl1, TermList tl2, const LPO& lpo);

  const LPO& _lpo;
  Stack<Node> _instructions;
  Node::BranchTag _res;
};

}
#endif
