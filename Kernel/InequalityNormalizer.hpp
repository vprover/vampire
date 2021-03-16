/*
 * File InequalityNormalizer.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __INEQUALITY_NORMALIZER_HPP__
#define __INEQUALITY_NORMALIZER_HPP__

#include "Lib/Int.hpp"
#include "Forwards.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)


namespace Kernel {
  using Inferences::PolynomialEvaluation;
  
  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term >= 0 or term > 0 (for Reals and Rationals)
   * or   term >= 0             (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    Perfect<Polynom<NumTraits>> _term;
    bool _strict;

  public:
    InequalityLiteral(Perfect<Polynom<NumTraits>> term, bool strict) 
      : _term(term), _strict(strict) {}

    friend class InequalityNormalizer;

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return *_term; }

    /* 
     * returns whether this is a strict inequality (i.e. >), 
     * or a non-strict one (i.e. >=) 
     * */
    bool strict() const
    { return _strict; }

    friend std::ostream& operator<<(std::ostream& out, InequalityLiteral const& self) 
    { return out << self._term << (self._strict ? " > " : " >= ") << "0"; }

    Literal* denormalize() const
    {
      auto p = strict() ? NumTraits::greater : NumTraits::geq;
      return p(true, term().denormalize(), NumTraits::zero());
    }
  };

  class InequalityNormalizer {
    // Map<Literal*, Option<InequalityLiteral>> _normalized;
    PolynomialEvaluation _eval;

  public:
    InequalityNormalizer(PolynomialEvaluation eval) 
      : _eval(eval) {  }

    template<class NumTraits> Option<InequalityLiteral<NumTraits>> normalize(Literal* lit) const;
  };



}

////////////////////////////////////////////////////////////////////////////
// impl InequalityLiteral
/////////////////////////////
  
namespace Kernel {

  template<class NumTraits>
  Option<InequalityLiteral<NumTraits>> InequalityNormalizer::normalize(Literal* lit) const
  {
    CALL("InequalityLiteral<NumTraits>::fromLiteral(Literal*)")
    DEBUG("in: ", *lit, " (", NumTraits::name(), ")")

    auto impl = [&]() {

      constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

      using Opt = Option<InequalityLiteral<NumTraits>>;

      auto f = lit->functor();
      if (!theory->isInterpretedPredicate(f))
        return Opt();

      auto itp = theory->interpretPredicate(f);


      bool strict;
      TermList l, r; // <- we rewrite to l < r or l <= r
      switch(itp) {
        case NumTraits::leqI: /* l <= r */
          l = *lit->nthArgument(0);
          r = *lit->nthArgument(1);
          strict = false;
          break;

        case NumTraits::geqI: /* l >= r ==> r <= l */
          l = *lit->nthArgument(1);
          r = *lit->nthArgument(0);
          strict = false;
          break;

        case NumTraits::lessI: /* l < r */
          l = *lit->nthArgument(0);
          r = *lit->nthArgument(1);
          strict = true;
          break;

        case NumTraits::greaterI: /* l > r ==> r < l */
          l = *lit->nthArgument(1);
          r = *lit->nthArgument(0);
          strict = true;
          break;

        default: 
          return Opt();
      }

      if (lit->isNegative()) {
        std::swap(l, r);
        strict = !strict;
      }

      if (isInt && !strict) {
        /* l <= r ==> l < r + 1 */
        r = NumTraits::add(r, NumTraits::one());
        strict = true;
      }

      /* l < r ==> r > l ==> r - l > 0 */
      auto t = NumTraits::add(r, NumTraits::minus(l));

      ASS(!isInt || strict)
      auto tt = TypedTermList(t, NumTraits::sort);
      auto norm = Kernel::normalizeTerm(tt);
      auto simpl = _eval.evaluate(norm).unwrapOr(norm);
      return Opt(InequalityLiteral<NumTraits>(simpl.wrapPoly<NumTraits>(), strict));
    };
    auto out = impl();
    DEBUG("out: ", out);
    return out;
  }

} // namespace Kernel

#undef DEBUG
#endif // __INEQUALITY_NORMALIZER_HPP__

