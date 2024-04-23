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

template<class Applicator>
struct AppliedTermLPO
{
  TermList term;
  bool termAboveVar;
  const Applicator& applicator;

  AppliedTermLPO(TermList t, const Applicator& applicator, bool aboveVar)
    : term(aboveVar && t.isVar() ? applicator(t) : t),
      termAboveVar(aboveVar && t.isVar() ? false : aboveVar), applicator(applicator) {}

  bool operator==(const AppliedTermLPO& other) const {
    // std::cout << "operator==" << term << " " << other.term << std::endl;
    // std::cout << "          " << (termAboveVar?applicator(term):term) << " " << (other.termAboveVar?other.applicator(other.term):other.term) << std::endl;
    if (!termAboveVar && !other.termAboveVar) {
      return term == other.term;
    }
    if (term.isVar() || other.term.isVar()) {
      return false;
    }
    auto t = term.term();
    auto o = other.term.term();
    if (t->functor()!=o->functor()) {
      return false;
    }
    for (unsigned i = 0; i < t->arity(); i++) {
      if (!(AppliedTermLPO(*t->nthArgument(i),applicator,termAboveVar)==AppliedTermLPO(*o->nthArgument(i),other.applicator,other.termAboveVar))) {
        return false;
      }
    }
    return true;
  }
  bool operator!=(const AppliedTermLPO& other) const {
    return !(*this==other);
  }
};

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
  template<class Applicator>
  Result isGreaterOrEq(AppliedTermLPO<Applicator>&& tt1, AppliedTermLPO<Applicator>&& tt2, const Applicator& applicator) const;
  void showConcrete(std::ostream&) const override;

  struct Node;

  bool isGreater(TermList lhs, TermList rhs, const std::function<TermList(TermList)>& applicator) const override;
  Node* preprocessComparison(TermList tl1, TermList tl2, Result expected) const;

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

  template<class Applicator>
  [[nodiscard]] bool alpha_gt(TermList* tl, unsigned arity, bool argsAboveVar, AppliedTermLPO<Applicator> t, const Applicator& applicator) const;
  template<class Applicator>
  [[nodiscard]] bool clpo_gt(AppliedTermLPO<Applicator> t1, AppliedTermLPO<Applicator> tl2, const Applicator& applicator) const;
  template<class Applicator>
  [[nodiscard]] bool lpo_gt(AppliedTermLPO<Applicator> t1, AppliedTermLPO<Applicator> tl2, const Applicator& applicator) const;
  template<class Applicator>
  [[nodiscard]] bool lexMAE_gt(AppliedTermLPO<Applicator> s, AppliedTermLPO<Applicator> t, TermList* sl, TermList* tl, unsigned arity, const Applicator& applicator) const;
  template<class Applicator>
  [[nodiscard]] bool majo_gt(AppliedTermLPO<Applicator> s, TermList* tl, unsigned arity, bool argsAboveVar, const Applicator& applicator) const;

  mutable DHMap<std::tuple<TermList,TermList,Result>,Node*> _comparisons;
};

}
#endif
