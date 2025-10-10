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
 * @file HOLUtils.cpp
 */

#include "HOLUtils.hpp"

#include "Kernel/HOL/HOL.hpp"
#include "Lib/Environment.hpp"

namespace Test::HOL {

using namespace Kernel;

std::string termListToString(TermList t, Options::HPrinting opt) {
  const auto prev = env.options->holPrinting();
  env.options->setHolPrinting(opt);
  const auto s = t.toString();
  env.options->setHolPrinting(prev);

  return s;
}

TypedTermList lam(std::initializer_list<TypedTermList> typedVars, TypedTermList body) {
  ASS(typedVars.size() > 0)

  std::vector<unsigned> vars;
  std::vector<TermList> varSorts;
  for (const auto& term : typedVars) {
    vars.push_back(term.var());
    varSorts.push_back(term.sort());
  }

  TermList sort;
  const auto term = ::HOL::create::lambda(typedVars.size(), vars.data(), varSorts.data(), body, &sort);
  return {TermList(term), sort};
}

TypedTermList app(TypedTermList lhs, TypedTermList rhs) {
  ASS(lhs.sort().isArrowSort())

  auto [domain, result] = lhs.sort().asPair();

  ASS(domain == rhs.sort())

  return {::HOL::create::app(domain, result, lhs, rhs), result};
}

TypedTermList app(const std::initializer_list<TypedTermList>& terms) {
  const auto size = terms.size();

  ASS(size > 0)
  auto a = std::data(terms);
  TypedTermList res = a[0];

  for (std::size_t i = 0; i + 1 < size; ++i) {
    res = app(res, a[i+1]);
  }

  return res;
}

static TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

static TypedTermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return {TermList(Term::createConstant(nameIndex)), sort};
}

Defs::Defs() {
  srt = mkAtomicSort("srt");
  fSrt = TermList(AtomicSort::arrowSort(srt, srt));
  a = mkConst("a", srt);
  f = mkConst("f", fSrt);
  f2 = mkConst("f2", AtomicSort::arrowSort({srt, srt, srt}));
  f3 = mkConst("f3", AtomicSort::arrowSort({srt, srt, srt, srt}));
  g = mkConst("g", AtomicSort::arrowSort(fSrt, srt));
  h = mkConst("h", AtomicSort::arrowSort({fSrt, srt, srt}));
}

Defs* Defs::_instance = nullptr;

Defs* Defs::instance() {
  if (_instance == nullptr)
    _instance = new Defs();

  return _instance;
}

TypedTermList x(unsigned idx, std::optional<TermList> sort) {
  return {TermList::var(idx), sort.value_or(Defs::instance()->srt)};
}

TypedTermList id(std::optional<TermList> sort) {
  const auto s = sort.value_or(Defs::instance()->srt);

  return lam(x(0, s), x(0, s));
}

TypedTermList db(int index, std::optional<TermList> sort) {
  TermList s = sort.value_or(Defs::instance()->srt);
  return {::HOL::getDeBruijnIndex(index, s), s};
}

TypedTermList LAM(TermList varSort, TypedTermList body) {
  return {::HOL::create::namelessLambda(varSort, body.sort(), body.untyped()), AtomicSort::arrowSort(varSort, body.sort())};
}

} // namespace Test::HOL