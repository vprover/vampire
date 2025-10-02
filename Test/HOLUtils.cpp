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

TermList lam(std::initializer_list<unsigned> vars, std::initializer_list<TermList> varSorts, TypedTermList body) {
  return TermList(::HOL::create::lambda(vars, varSorts, body));
}

TermList lam(TypedTermList var, TypedTermList body) {
  return TermList(::HOL::create::lambda({var.var()}, {var.sort()}, body));
}

static TermList mkAtomicSort(const std::string& name) {
  return TermList(AtomicSort::createConstant(name));
}

static TermList mkConst(const std::string& name, TermList sort) {
  unsigned nameIndex = env.signature->addFunction(name, 0);
  env.signature->getFunction(nameIndex)->setType(OperatorType::getFunctionType({}, sort));
  return TermList(Term::createConstant(nameIndex));
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