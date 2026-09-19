/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"

using namespace Kernel;
using namespace Lib;

TEST_FUN(namedSymbolsKeepRegistrationSemantics)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  bool added = false;
  auto f = sig.function("builder_symbol", type, added).introduced().skolem();
  ASS(added);
  ASS_EQ(sig.getFunction(f.number()), &f.symbol());
  ASS(f->introduced() && f->skolem());
  auto again = sig.function("builder_symbol", type, added);
  ASS(!added);
  ASS_EQ(again.number(), f.number());
  ASS(!again->introduced());
  ASS(again->skolem());

  auto p = sig.predicate("builder_symbol", OperatorType::getPredicateType({}), added).label();
  ASS(added);
  ASS_EQ(sig.getPredicate(p.number()), &p.symbol());
  ASS(p->label() && p->protectedSymbol());
  ASS_EQ(sig.predicate("builder_symbol", p->type(), added).number(), p.number());
  ASS(!added);

  auto tc = sig.typeConstructor("builder_symbol", 0, added);
  ASS(added);
  ASS_EQ(sig.getTypeCon(tc.number()), &tc.symbol());
  ASS_EQ(sig.typeConstructor("builder_symbol", 0, added).number(), tc.number());
  ASS(!added);
  ASS_EQ(sig.function("builder_symbol", type).number(), f.number());
  ASS_EQ(sig.predicate("builder_symbol", p->type()).number(), p.number());
  ASS_EQ(sig.typeConstructor("builder_symbol", 0).number(), tc.number());
}

TEST_FUN(freshSymbolsKeepFlagsAndStableHandles)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::boolSort());
  env.colorUsed = true;
  auto f = sig.freshFunction(type, "builder", "suffix").skolem().skipCongruence().protect().color(COLOR_LEFT);
  ASS_EQ(sig.getFunction(f.number()), &f.symbol());
  ASS(f->introduced() && f->skip() && f->skolem());
  ASS(f->skipCongruence() && f->protectedSymbol());
  ASS_EQ(f->color(), COLOR_LEFT);
  ASS_EQ(f->type(), type);
  ASS_EQ(f->name().substr(f->name().size() - 7), "_suffix");
  ASS_NEQ(sig.freshFunction(type, "builder", "suffix").number(), f.number());

  auto p = sig.freshPredicate(OperatorType::getPredicateType({}), "builder").answerPredicate().skipCongruence();
  ASS_EQ(sig.getPredicate(p.number()), &p.symbol());
  ASS(p->introduced() && p->skip() && p->answerPredicate());
  ASS(p->protectedSymbol() && p->skipCongruence());
  auto tc = sig.freshTypeConstructor(1, "builder").skolem();
  ASS_EQ(sig.getTypeCon(tc.number()), &tc.symbol());
  ASS(tc->introduced() && tc->skip() && tc->skolem());
  ASS_EQ(tc->arity(), 1u);

  for (unsigned i = 0; i < 1000; ++i) {
    sig.freshFunction(type, "grow");
    sig.freshPredicate(p->type(), "grow");
    sig.freshTypeConstructor(0, "grow");
  }
  ASS_EQ(sig.getFunction(f.number()), &f.symbol());
  ASS_EQ(sig.getPredicate(p.number()), &p.symbol());
  ASS_EQ(sig.getTypeCon(tc.number()), &tc.symbol());
  ASS(f->skolem() && p->answerPredicate() && tc->skolem());

  auto proxy = sig.freshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort(), AtomicSort::defaultSort()}), "proxy")
    .equalityProxy().skipCongruence();
  ASS(proxy->equalityProxy() && proxy->skipCongruence());
  auto discr = sig.freshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort()}), "discr")
    .termAlgebraDiscriminator();
  ASS(discr->termAlgebraDiscriminator());
  auto constructor = sig.freshFunction(type, "constructor").termAlgebraConstructor();
  ASS(constructor->termAlgebraCons());
  auto destructor = sig.freshFunction(type, "destructor").termAlgebraDestructor();
  ASS(destructor->termAlgebraDest());
  auto named = sig.function("builder_flags", type).introduced().skip();
  ASS(named->introduced() && named->skip());
}
