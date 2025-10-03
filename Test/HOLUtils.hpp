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

namespace Test::HOL {

using namespace Kernel;

TypedTermList lam(std::initializer_list<unsigned> vars, std::initializer_list<TermList> varSorts, TypedTermList body);
TypedTermList lam(std::initializer_list<TypedTermList> vars, TypedTermList body);
TypedTermList lam(TypedTermList var, TypedTermList body);

TypedTermList app(TypedTermList lhs, TypedTermList rhs);
TypedTermList app(const std::initializer_list<TypedTermList>& terms);

TypedTermList mkConst(const std::string& name, TermList sort);

class Defs {
  static Defs* _instance;
  Defs();
public:
  static Defs* instance();

  TermList srt;
  TermList fSrt;
  TermList x0;
  TermList x1;
  TypedTermList a;
  TypedTermList f;
};

} // namespace Test::HOL

#endif // __HOLUtils__