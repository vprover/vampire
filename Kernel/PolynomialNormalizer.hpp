/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __POLYNOMIAL_NORMALIZER_HPP__
#define __POLYNOMIAL_NORMALIZER_HPP__

#include "Forwards.hpp"

#include "Term.hpp"
#include "NumTraits.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include "Lib/Option.hpp"
#include "Kernel/Polynomial.hpp"
#include "Inferences/InferenceEngine.hpp"


namespace Kernel {

using LitSimplResult = Inferences::SimplifyingGeneratingLiteralSimplification::Result;

/* non-shared monom */
template<class NumTraits>
struct PreMonom
{
  using Numeral = typename NumTraits::ConstantType;

  PreMonom(Numeral n, std::initializer_list<PolyNf> factors) : numeral(std::move(n)), factors() 
  { this->factors->init(factors); }

  PreMonom(Numeral n)
    : PreMonom(std::move(n), {}) {}

  PreMonom(std::initializer_list<PolyNf> factors) 
    : PreMonom(Numeral(1), factors) {}

  Numeral numeral;
  RStack<PolyNf> factors;
  friend std::ostream& operator<<(std::ostream& out, PreMonom const& self)
  { return out << Output::cat("PreMonom(", self.numeral, ", ", self.factors, ")"); }
};

using NormalizationResult = Coproduct<PolyNf 
        , Polynom< IntTraits>
        , Polynom< RatTraits>
        , Polynom<RealTraits>
        , PreMonom< IntTraits>
        , PreMonom< RatTraits>
        , PreMonom<RealTraits>
        >;

PolyNf normalizeTerm(TypedTermList t, bool& simplified);

inline PolyNf normalizeTerm(TypedTermList t) {
  bool dummy;
  return normalizeTerm(t, dummy);
}

inline PolyNf normalizeTerm(TermList t, SortId sort)
{ return normalizeTerm(TypedTermList(t,sort)); }

inline PolyNf normalizeTerm(Term* t)
{ return normalizeTerm(TypedTermList(t)); }
} // namespace Kernel

/** a memoization realized as a hashmap */
template<class Arg, class Result>
struct MemoNonVars 
{
  Map<Arg, Result> _memo;

public:
  MemoNonVars() : _memo(decltype(_memo)()) {}

  static bool isVar(PolyNf const& p) { return p.is<Variable>(); }
  static bool isVar(TermList const& p) { return p.isVar(); }

  template<class Init> Result getOrInit(Arg const& orig, Init init)
  { 
    return isVar(orig) 
      ? init()
      : _memo.getOrInit(Arg(orig), init);
  }

  Option<Result> get(const Arg& orig)
  { return isVar(orig) ? Option<Result>() : _memo.tryGet(orig).toOwned(); }
};


#endif // __POLYNOMIAL_NORMALIZER_HPP__
