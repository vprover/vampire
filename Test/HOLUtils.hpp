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
#include "Kernel/HOL/HOL.hpp"
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
using namespace Shell;

std::string termListToString(TermList t, Options::HPrinting opt);

TypedTermList lam(std::initializer_list<TypedTermList> vars, TypedTermList body);

template <class T>
void assertThrows(T f, const std::string& cond = "") {
  bool exceptionThrown = false;

  auto originalVal = ::HOL::catchViolations;
  ::HOL::catchViolations = true;
  try {
    f();
  }
  catch (const ::HOL::HOLError& err) {
    exceptionThrown = true;

    if (!cond.empty() && cond != err.cond) {
      std::string msg = "Expected condition '";
      msg.append(cond);
      msg.append("' but got '");
      msg.append(err.cond);
      msg.append("'");

      Debug::Assertion::violated(err.file, err.line, msg.c_str());
    }
  }

  if (!exceptionThrown)
    Debug::Assertion::violated(__FILE__, __LINE__, "No exception was thrown");

  ::HOL::catchViolations = originalVal;
}

inline TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

inline TypedTermList lam(TypedTermList var, TypedTermList body) {
  return lam({var}, body);
}

template <class T, class ...Ts>
TypedTermList app(TypedTermList arg1, T arg2, Ts... args) {
  ASS(arg1.sort().isArrowSort())

  auto [domain, result] = arg1.sort().asPair();

  ASS(domain == arg2.sort())

  TypedTermList t = {::HOL::create::app(domain, result, arg1, arg2), result};

  if constexpr (sizeof...(args) == 0)
    return t;
  else
    return app(t, args...);
}

class Defs {
  static Defs* _instance;
  Defs();
public:
  static Defs* instance();

  TermList srt, fSrt;
  TypedTermList a, f, f2, f3, g, h;
};

TypedTermList x(unsigned idx, std::optional<TermList> sort = std::nullopt);

TypedTermList id(std::optional<TermList> sort = std::nullopt);

TypedTermList db(int index, std::optional<TermList> sort = std::nullopt);

TypedTermList LAM(TermList varSort, TypedTermList body);

} // namespace Test::HOL

#endif // __HOLUtils__