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
  Result compare(TermList tl1, TermList tl2) const override;
  Result compare(AppliedTerm&& tl1, AppliedTerm&& tl2) const override;
  void showConcrete(std::ostream&) const override;

  bool isGreater(AppliedTerm&& tl1, AppliedTerm&& tl2) const override;

protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;
  Result comparePrecedences(const Term* t1, const Term* t2) const;

  Result cLMA(const AppliedTerm& s, const AppliedTerm& t, const TermList* sl, const TermList* tl, unsigned arity) const;
  Result cMA(const AppliedTerm& s, const AppliedTerm& t, const TermList* tl, unsigned arity) const;
  Result cAA(const AppliedTerm& s, const AppliedTerm& t, const TermList* sl, const TermList* tl, unsigned arity1, unsigned arity2) const;
  Result alpha(const TermList* sl, unsigned arity, const AppliedTerm& s, const AppliedTerm& t) const;
  Result clpo(const AppliedTerm& tl1, const AppliedTerm& tl2) const;
  Result lpo(const AppliedTerm& tl1, const AppliedTerm& tl2) const;
  Result lexMAE(const AppliedTerm& s, const AppliedTerm& t, const TermList* sl, const TermList* tl, unsigned arity) const;
  Result majo(const AppliedTerm& s, const AppliedTerm& t, const TermList* tl, unsigned arity) const;
};

}
#endif
