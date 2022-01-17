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
  CLASS_NAME(LPO);
  USE_ALLOCATOR(LPO);

  LPO(Problem& prb, const Options& opt) :
    PrecedenceOrdering(prb, opt)
  {}
  LPO(const DArray<int>& funcPrec, const DArray<int>& predPrec, const DArray<int>& predLevels, bool reverseLCM) :
    PrecedenceOrdering(funcPrec, predPrec, predLevels, reverseLCM)
  {}
  ~LPO() override = default;

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;
  void showConcrete(ostream&) const override;
protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;

  Result cLMA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  Result cMA(Term* t, TermList* tl, unsigned arity) const;
  Result cAA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity1, unsigned arity2) const;
  Result alpha(TermList* tl, unsigned arity, Term *t) const;
  Result clpo(Term* t1, TermList tl2) const;
  Result lpo(TermList tl1, TermList tl2) const;
  Result lexMAE(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  Result majo(Term* s, TermList* tl, unsigned arity) const;

};

}
#endif
