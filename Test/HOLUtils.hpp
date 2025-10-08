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
 * @file HOLUtils.hpp
 */

#ifndef __HOLUtils__
#define __HOLUtils__

#include "Kernel/Term.hpp"
#include "Kernel/TypedTermList.hpp"
#include "Shell/Options.hpp"

#include <optional>

namespace Test::HOL {

#define HOL_TEST_FUN(name)                 \
  void name ## _test_impl(const Defs&);    \
  TEST_FUN(name) {                         \
    env.setHigherOrder(true);              \
    name ## _test_impl(*Defs::instance()); \
  }                                        \
  void name ## _test_impl(const Defs& D)

using namespace Kernel;

std::string termListToString(TermList t, Shell::Options::HPrinting opt);

TypedTermList lam(std::initializer_list<TypedTermList> vars, TypedTermList body);

inline TypedTermList lam(TypedTermList var, TypedTermList body) {
  return lam({var}, body);
}

TypedTermList app(TypedTermList lhs, TypedTermList rhs);
TypedTermList app(const std::initializer_list<TypedTermList>& terms);

class Defs {
  static Defs* _instance;
  Defs();
public:
  static Defs* instance();

  static TypedTermList x(unsigned idx, std::optional<TermList> sort = std::nullopt);

  TermList srt, fSrt;
  TypedTermList a, f, f2, f3, g;
};

const auto x0 = Defs::x(0);
const auto x1 = Defs::x(1);
const auto x2 = Defs::x(2);

} // namespace Test::HOL

#endif // __HOLUtils__