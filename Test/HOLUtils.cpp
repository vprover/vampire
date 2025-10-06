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
  env.options->setHolPrinting(opt);
  return t.toString(true);
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

TypedTermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return {TermList(Term::createConstant(nameIndex)), sort};
}

Defs::Defs() {
  srt = mkAtomicSort("srt");
  fSrt = TermList(AtomicSort::arrowSort(srt, srt));
  x0 = TermList::var(0);
  x1 = TermList::var(1);
  a = {mkConst("a", srt), srt};
  f = {mkConst("f", fSrt), fSrt};
}

Defs* Defs::_instance = nullptr;

Defs* Defs::instance() {
  if (_instance == nullptr)
    _instance = new Defs();

  return _instance;
}

} // namespace Test::HOL