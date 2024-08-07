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

/**
 * Runtime specialized LPO ordering check, based on the LPO check
 * that has quadratic time complexity @see LPO::lpo.
 */
class LPOComparator
: public OrderingComparator
{
public:
  /** The runtime specialization happens in the constructor. */
  LPOComparator(TermList lhs, TermList rhs, const LPO& lpo);

  /** Executes the runtime specialized instructions with concrete substitution. */
  bool check(const SubstApplicator* applicator) override;
  std::string toString() const override;

  /**
   * Represents comparing check between two terms and branching
   * information based on the result. The comparison results in
   * either @b GREATER, @b EQUAL or @b INCOMPARABLE, hence there
   * are three branches.
   */
  struct Instruction {
    /**
     * Possible values for a branch, i.e. return the result
     * of the comparison, or jump to a different instruction.
     */
    enum class BranchTag : uint8_t {
      T_EQUAL,
      T_GREATER,
      T_INCOMPARABLE,
      T_JUMP,
    };

    struct Branch {
      BranchTag tag;
      uint16_t jump_pos; // jump positions are absolute

      std::tuple<BranchTag,uint16_t> asTuple() const
      { return std::make_tuple(tag, jump_pos); }

      IMPL_COMPARISONS_FROM_TUPLE(Branch);
      IMPL_HASH_FROM_TUPLE(Branch);

      static constexpr Branch eq() { return Branch{ BranchTag::T_EQUAL, 0 }; }
      static constexpr Branch gt() { return Branch{ BranchTag::T_GREATER, 0 }; }
      static constexpr Branch inc() { return Branch{ BranchTag::T_INCOMPARABLE, 0 }; }
      static constexpr Branch jump(uint16_t pos) { return Branch{ BranchTag::T_JUMP, pos }; }

      void update(Branch eqBranch, Branch gtBranch, Branch incBranch, unsigned jump_offset);
    };

    Instruction(TermList lhs, TermList rhs)
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

    std::tuple<TermList,TermList,Branch,Branch,Branch> asTuple() const
    { return std::make_tuple(lhs, rhs, bs[0], bs[1], bs[2]); }

    IMPL_COMPARISONS_FROM_TUPLE(Instruction);
    IMPL_HASH_FROM_TUPLE(Instruction);

    // two terms for the comparison
    TermList lhs;
    TermList rhs;
    // three branches for the three possible comparison results
    Branch bs[3];

  };

private:
  static pair<Stack<Instruction>,Instruction::BranchTag> majoChain(const LPO& lpo, TermList tl1, Term* t, unsigned i);
  static pair<Stack<Instruction>,Instruction::BranchTag> alphaChain(const LPO& lpo, Term* s, unsigned i, TermList tl2);
  static pair<Stack<Instruction>,Instruction::BranchTag>* createHelper(TermList tl1, TermList tl2, const LPO& lpo);

  bool _ready;

  /** This is non-empty if @b _res is @b BranchTag::T_JUMP */
  Stack<Instruction> _instructions;

  /** It contains the result of the comparison if the terms
   * are comparable, otherwise it contains @b BranchTag::T_JUMP
   * to indicate that @b _instructions have to be executed. */
  Instruction::BranchTag _res;
};

class LPOComparator2
: public OrderingComparator
{
public:
  /** The runtime specialization happens in the constructor. */
  LPOComparator2(TermList lhs, TermList rhs, const LPO& lpo);
  ~LPOComparator2() override;

  /** Executes the runtime specialized instructions with concrete substitution. */
  bool check(const SubstApplicator* applicator) override;
  std::string toString() const override;

  enum class BranchTag : uint8_t {
    T_EQUAL,
    T_GREATER,
    T_INCOMPARABLE,
    T_COMPARISON,
    T_UNKNOWN,
  };

  struct Node;

  struct Branch {
    BranchTag tag;
    Node* n;

    explicit Branch(BranchTag t) : tag(t), n(nullptr) {}
    explicit Branch(Node* n) : tag(BranchTag::T_UNKNOWN), n(n) {}
  };

  struct Node {
    Node(TermList lhs, TermList rhs)
      : lhs(lhs), rhs(rhs), eqBranch(BranchTag::T_EQUAL), gtBranch(BranchTag::T_GREATER), incBranch(BranchTag::T_INCOMPARABLE) {}

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

  friend ostream& operator<<(ostream& str, const LPOComparator2& comp);

  Branch _root;
};

}
#endif
