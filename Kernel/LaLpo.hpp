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

#include "Lib/DArray.hpp"
#include "Kernel/IRC.hpp"

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

  Comparison cmpFun(unsigned l, unsigned r) const;
  Comparison cmpPred(unsigned l, unsigned r) const;
  void show(ostream& out) const;
};

class LaLpo 
  : public Ordering
{
public:
  CLASS_NAME(LaLpo);
  USE_ALLOCATOR(LaLpo);

  LaLpo(LaLpo&& kbo) = default;
  LaLpo& operator=(LaLpo&& kbo) = default;
  explicit LaLpo(Precedence);

  virtual ~LaLpo() {}

  Result compare(Literal* l1, Literal* l2) const override;
  Result compare(TermList, TermList) const final override;

  void show(ostream& out) const final override;

  Comparison compareFunctors(unsigned fun1, unsigned fun2) const override { ASSERTION_VIOLATION }

  void setState(std::shared_ptr<IrcState> s) { _shared = std::move(s); }

private:
  Comparison cmpFun(Term* s, Term* t) const;

  Precedence _prec;
  std::shared_ptr<IrcState> _shared;
};

} // namespace Kernel

#endif // __LINEAR_ARITHMETIC_LPO__
