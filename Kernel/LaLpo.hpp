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
 * @file LaLpo.hpp
 *
 * Defines a Knuth-Bendix Ordering for linear arithmetic. This ignores numeral multiplications,
 * (i.e. it considers terms t and nt where n is a numeral as equaivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __LINEAR_ARITHMETIC_LPO__
#define __LINEAR_ARITHMETIC_LPO__

#include "Forwards.hpp"

#include "Kernel/SubstHelper.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/ALASCA.hpp"

#include "Ordering.hpp"
#include "Lib/DArray.hpp"

namespace Kernel {

using namespace Lib;

// TODO move to appropriate point
class Precedence final 
{
  DArray<int> _funPrec;
  DArray<int> _predPrec;
public:
  Precedence(Precedence&&) = default;
  Precedence& operator=(Precedence&&) = default;
  Precedence(DArray<int> funPrec, DArray<int> predPrec)
    : _funPrec(std::move(funPrec))
    , _predPrec(std::move(predPrec)) {}

  Precedence(Problem& prb, const Options& opts) 
    : Precedence(
        PrecedenceOrdering::funcPrecFromOpts(prb, opts),
        PrecedenceOrdering::predPrecFromOpts(prb, opts)) {}

  static Precedence random();

  

  DArray<int> const&  funPrec() const { return  _funPrec; }
  DArray<int> const& predPrec() const { return _predPrec; }

  Comparison cmpFun(unsigned l, unsigned r) const;
  Comparison cmpPred(unsigned l, unsigned r) const;
  void show(std::ostream& out) const;
};

class LaLpo 
  : public Ordering
{
public:
  USE_ALLOCATOR(LaLpo);

  LaLpo(LaLpo&& kbo) = default;
  LaLpo& operator=(LaLpo&& kbo) = default;
  explicit LaLpo(Precedence);

  LaLpo(Problem& prb, const Options& opts) 
    : LaLpo(Precedence(prb,opts)) {}

  virtual ~LaLpo() {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final override;
  Result compare(AppliedTerm t1, AppliedTerm t2) const override;
  bool isGreater(AppliedTerm t1, AppliedTerm t2) const override
  { 
    // TODO more efficient impl (?)
    return compare(t1, t2) == Result::GREATER; }

  void show(std::ostream& out) const final override;


  enum class Pred 
  { Eq, Neq, Greater, Geq, Uninterpreted };

  struct Lit {
    Literal* orig;
    Pred pred;
    auto interpreted() const { return pred != Pred::Uninterpreted; }
    auto sort() const { 
      ASS(interpreted())
      return SortHelper::getArgSort(orig, 0);
    }
    Lit(Literal* l) 
      : orig(l)
      , pred(
          l->functor() == 0 
            ? (l->isPositive() ? Pred::Eq : Pred::Neq)
            : tryNumTraits([&](auto numTraits) { 
                  auto f = l->functor();
                  return f == numTraits.greaterF() ? Option<Pred>(Pred::Greater)
                       : f == numTraits.    geqF() ? Option<Pred>(Pred::Geq    )
                       : Option<Pred>();
                })
              .unwrapOr(Pred::Uninterpreted)
          ) {}
  };
private:
  Comparison cmpFun(Term* s, Term* t) const;

  Precedence _prec;
};

} // namespace Kernel

#endif // __LINEAR_ARITHMETIC_LPO__
