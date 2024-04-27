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
 * @file LPO.hpp
 * Defines class LPO for instances of the lexicographic path ordering
 *
 * The implementation of LPO follows "THINGS TO KNOW WHEN IMPLEMENTING
 * LPO" (Löchner, 2006), in particular the function called "clpo_6".
 */

#ifndef __LPO__
#define __LPO__

#include "Forwards.hpp"

#include "SubstHelper.hpp"

#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;
using namespace std;

/**
 * Class for instances of the lexicographic path orderings
 */
class LPO
: public PrecedenceOrdering
{
public:
  LPO(Problem& prb, const Options& opt) :
    PrecedenceOrdering(prb, opt)
  {}
  LPO(const DArray<int>& funcPrec, const DArray<int>& typeConPrec, 
      const DArray<int>& predPrec, const DArray<int>& predLevels, bool reverseLCM) :
    PrecedenceOrdering(funcPrec, typeConPrec, predPrec, predLevels, reverseLCM)
  {}
  ~LPO() override = default;

  using PrecedenceOrdering::compare;

  struct Node {
    enum class BranchTag {
      T_EQUAL,
      T_GREATER,
      T_INCOMPARABLE,
      T_JUMP,
    };

    struct Branch {
      BranchTag tag;
      unsigned jump_pos;
      bool operator==(const Branch& other) const {
        return tag == other.tag && jump_pos == other.jump_pos;
      }
    };

    Node(TermList lhs, TermList rhs)
      : lhs(lhs), rhs(rhs), eqBranch({ BranchTag::T_EQUAL, 0 }), gtBranch({ BranchTag::T_GREATER, 0 }), incBranch({ BranchTag::T_INCOMPARABLE, 0 }) {}

    TermList lhs;
    TermList rhs;
    Branch eqBranch;
    Branch gtBranch;
    Branch incBranch;

    friend ostream& operator<<(ostream& out, const Node& n);
    friend ostream& operator<<(ostream& out, const Branch& b);
    friend ostream& operator<<(ostream& out, const BranchTag& bt);
  };

  std::pair<Stack<Node>*,Node::BranchTag> preprocessComparison(TermList tl1, TermList tl2) const;

  Result compare(TermList tl1, TermList tl2) const override;
  Result compare(AppliedTerm tl1, AppliedTerm tl2) const override;
  void showConcrete(std::ostream&) const override;

  bool isGreater(AppliedTerm tl1, AppliedTerm tl2) const override;
  bool isGreater(TermList lhs, TermList rhs, const SubstApplicator* applicator, Stack<Instruction>*& instructions) const override;

protected:
  struct ResultNode;
  struct ComparisonNode;
  struct ConditionalNode;

  Result comparePredicates(Literal* l1, Literal* l2) const override;
  Result comparePrecedences(const Term* t1, const Term* t2) const;

  Result cLMA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const;
  Result cMA(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const;
  Result cAA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity1, unsigned arity2) const;
  Result alpha(const TermList* sl, unsigned arity, AppliedTerm s, AppliedTerm t) const;
  Result clpo(AppliedTerm tl1, AppliedTerm tl2) const;
  Result lpo(AppliedTerm tl1, AppliedTerm tl2) const;
  Result lexMAE(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const;
  Result majo(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const;

  mutable DHMap<std::pair<TermList,TermList>,std::pair<Stack<Node>*,Node::BranchTag>> _comparisons;
};

}
#endif
