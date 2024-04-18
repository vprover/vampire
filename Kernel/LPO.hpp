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
  [[nodiscard]] Result compare(TermList tl1, TermList tl2) const override;
  void showConcrete(std::ostream&) const override;

  bool isGreater(AppliedTerm&& lhs, AppliedTerm&& rhs) const override;

protected:
  [[nodiscard]] Result comparePredicates(Literal* l1, Literal* l2) const override;
  [[nodiscard]] Result comparePrecedences(Term* t1, Term* t2) const;

  [[nodiscard]] Result cLMA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  [[nodiscard]] Result cMA(Term* t, TermList* tl, unsigned arity) const;
  [[nodiscard]] Result cAA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity1, unsigned arity2) const;
  [[nodiscard]] Result alpha(TermList* tl, unsigned arity, Term *t) const;
  [[nodiscard]] Result clpo(Term* t1, TermList tl2) const;
  [[nodiscard]] Result lpo(TermList tl1, TermList tl2) const;
  [[nodiscard]] Result lexMAE(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  [[nodiscard]] Result majo(Term* s, TermList* tl, unsigned arity) const;

  [[nodiscard]] Result alpha_gt(TermList* tl, unsigned arity, bool argsAboveVar, const SubstApplicator& argApplicator, AppliedTerm t) const;
  [[nodiscard]] Result lpo_gt(AppliedTerm tl1, AppliedTerm tl2) const;
  [[nodiscard]] Result lexMAE_gt(AppliedTerm s, AppliedTerm t, TermList* sl, TermList* tl, unsigned arity) const;
  [[nodiscard]] Result majo_gt(AppliedTerm s, TermList* tl, unsigned arity, bool argsAboveVar, const SubstApplicator& argApplicator) const;
};

}
#endif
