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
  LPO(Problem& prb, const Options& opt) :
    PrecedenceOrdering(prb, opt)
  {}
  LPO(const DArray<int>& funcPrec, const DArray<int>& typeConPrec, 
      const DArray<int>& predPrec, const DArray<int>& predLevels, bool reverseLCM) :
    PrecedenceOrdering(funcPrec, typeConPrec, predPrec, predLevels, reverseLCM)
  {}
  ~LPO() override = default;

  using PrecedenceOrdering::compare;
  VWARN_UNUSED Result compare(TermList tl1, TermList tl2) const override;
  VWARN_UNUSED bool isGreater(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, const Indexing::TermQueryResult* qr) const override;
  VWARN_UNUSED bool isGreater(TermList tl1, TermList tl2, const VarOrder& vo) const override;
  VWARN_UNUSED bool makeGreater(TermList tl1, TermList tl2, VarOrder& vo) const override;
  void showConcrete(std::ostream&) const override;
protected:
  VWARN_UNUSED Result comparePredicates(Literal* l1, Literal* l2) const override;
  VWARN_UNUSED Result comparePrecedences(Term* t1, Term* t2) const;

  VWARN_UNUSED Result cLMA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  VWARN_UNUSED Result cMA(Term* t, TermList* tl, unsigned arity) const;
  VWARN_UNUSED Result cAA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity1, unsigned arity2) const;
  VWARN_UNUSED Result alpha(TermList* tl, unsigned arity, Term *t) const;
  VWARN_UNUSED Result clpo(Term* t1, TermList tl2) const;
  VWARN_UNUSED Result lpo(TermList tl1, TermList tl2) const;
  VWARN_UNUSED Result lexMAE(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const;
  VWARN_UNUSED Result majo(Term* s, TermList* tl, unsigned arity) const;

  VWARN_UNUSED bool alpha_gt(TermList* tl, unsigned arity, Term *t, const VarOrder& vo) const;
  VWARN_UNUSED bool clpo_gt(Term* t1, TermList tl2, const VarOrder& vo) const;
  VWARN_UNUSED bool lpo_gt(TermList tl1, TermList tl2, const VarOrder& vo) const;
  VWARN_UNUSED bool lexMAE_gt(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity, const VarOrder& vo) const;
  VWARN_UNUSED bool majo_gt(Term* s, TermList* tl, unsigned arity, const VarOrder& vo) const;

  VWARN_UNUSED bool alpha_mgt(TermList* tl, unsigned arity, Term *t, VarOrder& vo) const;
  VWARN_UNUSED bool clpo_mgt(Term* t1, TermList tl2, VarOrder& vo) const;
  VWARN_UNUSED bool lpo_mgt(TermList tl1, TermList tl2, VarOrder& vo) const;
  VWARN_UNUSED bool lexMAE_mgt(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity, VarOrder& vo) const;
  VWARN_UNUSED bool majo_mgt(Term* s, TermList* tl, unsigned arity, VarOrder& vo) const;
};

}
#endif