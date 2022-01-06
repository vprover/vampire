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
 * @file QKbo.hpp
 *
 * Defines a Knuth-Bendix Ordering for linear arithmetic. This ignores numeral multiplications,
 * (i.e. it considers terms t and nt where n is a numeral as equaivalent). Further it is not sensitive to
 * bracketing or permuting of multiplications and additions.
 */

#ifndef __QKbo__
#define __QKBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Kernel/IRC.hpp"

#include "Ordering.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/LaLpo.hpp"
#include "Kernel/KBO.hpp"

namespace Kernel {

using namespace Lib;

class QKbo 
  : public Ordering
{
public:
  CLASS_NAME(QKbo);
  USE_ALLOCATOR(QKbo);

  QKbo(QKbo&& kbo) = default;
  QKbo& operator=(QKbo&& kbo) = default;
  explicit QKbo(Precedence);

  QKbo(Problem& prb, const Options& opts) 
    : QKbo(Precedence(prb,opts)) {}

  virtual ~QKbo() {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final override;

  void show(ostream& out) const final override;

  Comparison compareFunctors(unsigned fun1, unsigned fun2) const override { ASSERTION_VIOLATION }

  void setState(std::shared_ptr<IrcState> s) { _shared = std::move(s); }

private:
  using FlatSum = Stack<std::tuple<Option<TermList>, RationalConstantType>>;
  Ordering::Result cmpSum(FlatSum const& l, FlatSum const& r) const;
  FlatSum flatWithCoeffs(TermList t) const;
  Result cmpNonAbstr(TermList, TermList) const;
  Option<TermList> abstr(TermList) const;

  Precedence _prec;
  std::shared_ptr<IrcState> _shared;
  KBO _kbo;
};

} // namespace Kernel

#endif // __QKbo__
