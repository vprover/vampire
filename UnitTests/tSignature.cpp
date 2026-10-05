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
#include <type_traits>
#include <utility>

using namespace Kernel;
using namespace Lib;

static_assert(std::is_same_v<decltype(std::declval<Signature&>().getFunction(0)), const Signature::Symbol*>);
static_assert(std::is_same_v<decltype(std::declval<const Signature&>().getPredicate(0)), const Signature::Symbol*>);
static_assert(std::is_same_v<decltype(std::declval<Signature&>().getTypeCon(0)), const Signature::Symbol*>);

TEST_FUN(namedSymbolsKeepRegistrationSemantics)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  bool added = false;
  auto f = sig.addFunction("symbol_symbol", type, added)->markIntroduced()->markSkolem();
  ASS(added);
  ASS_EQ(sig.getFunction(f->number()), f);
  ASS(f->introduced() && f->skolem());
  auto again = sig.addFunction("symbol_symbol", type, added);
  ASS(!added);
  ASS_EQ(again->number(), f->number());
  ASS(!again->introduced());
  ASS(again->skolem());

  auto p = sig.addPredicate("symbol_symbol", OperatorType::getPredicateType({}), added)->markLabel();
  ASS(added);
  ASS_EQ(sig.getPredicate(p->number()), p);
  ASS(p->label() && p->protectedSymbol());
  ASS_EQ(sig.addPredicate("symbol_symbol", p->type(), added)->number(), p->number());
  ASS(!added);

  auto tc = sig.addTypeCon("symbol_symbol", 0, added);
  ASS(added);
  ASS_EQ(sig.getTypeCon(tc->number()), tc);
  ASS_EQ(sig.addTypeCon("symbol_symbol", 0, added)->number(), tc->number());
  ASS(!added);
  ASS_EQ(sig.addFunction("symbol_symbol", type)->number(), f->number());
  ASS_EQ(sig.addPredicate("symbol_symbol", p->type())->number(), p->number());
  ASS_EQ(sig.addTypeCon("symbol_symbol", 0)->number(), tc->number());
}

TEST_FUN(freshSymbolsKeepFlagsAndStableHandles)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::boolSort());
  env.colorUsed = true;
  auto f = sig.addFreshFunction(type, "symbol", "suffix")->markSkolem()->markSkipCongruence()->markProtected()->addColor(COLOR_LEFT);
  ASS_EQ(sig.getFunction(f->number()), f);
  ASS(f->introduced() && f->skip() && f->skolem());
  ASS(f->skipCongruence() && f->protectedSymbol());
  ASS_EQ(f->color(), COLOR_LEFT);
  ASS_EQ(f->type(), type);
  ASS_EQ(f->name().substr(f->name().size() - 7), "_suffix");
  ASS_NEQ(sig.addFreshFunction(type, "symbol", "suffix")->number(), f->number());

  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({}), "symbol")->markAnswerPredicate()->markSkipCongruence();
  ASS_EQ(sig.getPredicate(p->number()), p);
  ASS(p->introduced() && p->skip() && p->answerPredicate());
  ASS(p->protectedSymbol() && p->skipCongruence());
  auto tc = sig.addFreshTypeCon(1, "symbol")->markSkolem();
  ASS_EQ(sig.getTypeCon(tc->number()), tc);
  ASS(tc->introduced() && tc->skip() && tc->skolem());
  ASS_EQ(tc->arity(), 1u);

  for (unsigned i = 0; i < 1000; ++i) {
    sig.addFreshFunction(type, "grow");
    sig.addFreshPredicate(p->type(), "grow");
    sig.addFreshTypeCon(0, "grow");
  }
  ASS_EQ(sig.getFunction(f->number()), f);
  ASS_EQ(sig.getPredicate(p->number()), p);
  ASS_EQ(sig.getTypeCon(tc->number()), tc);
  ASS(f->skolem() && p->answerPredicate() && tc->skolem());

  auto proxy = sig.addFreshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort(), AtomicSort::defaultSort()}), "proxy")
    ->markEqualityProxy()->markSkipCongruence();
  ASS(proxy->equalityProxy() && proxy->skipCongruence());
  auto discr = sig.addFreshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort()}), "discr")
    ->markTermAlgebraDiscriminator();
  ASS(discr->termAlgebraDiscriminator());
  auto constructor = sig.addFreshFunction(type, "constructor")->markTermAlgebraCons();
  ASS(constructor->termAlgebraCons());
  auto destructor = sig.addFreshFunction(type, "destructor")->markTermAlgebraDest();
  ASS(destructor->termAlgebraDest());
  auto named = sig.addFunction("symbol_flags", type)->markIntroduced()->markSkip();
  ASS(named->introduced() && named->skip());
}

TEST_FUN(postRegistrationUpdatesPreserveIdentity)
{
  auto& sig = *env.signature;
  auto f = sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "existing");
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({}), "existing");
  auto functions = sig.functions();
  auto predicates = sig.predicates();
  sig.protectFunction(f->number());
  sig.markAnswerPredicate(p->number());
  ASS(f->introduced() && f->protectedSymbol());
  ASS(p->introduced() && p->answerPredicate() && p->protectedSymbol());
  ASS_EQ(sig.getFunction(f->number()), f);
  ASS_EQ(sig.getPredicate(p->number()), p);
  ASS_EQ(sig.functions(), functions);
  ASS_EQ(sig.predicates(), predicates);
}

TEST_FUN(specializedHelpersKeepFlags)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  auto predType = OperatorType::getPredicateType({});
  auto f = sig.addSkolemFunction(type, "test");
  auto p = sig.addSkolemPredicate(predType, "test");
  auto tc = sig.addSkolemTypeCon(1);
  for (auto symbol : {f, p, tc}) {
    ASS(symbol->skolem() && symbol->introduced() && symbol->skip());
    ASS_EQ(symbol->name().substr(0, 2), "sK");
  }
  for (auto symbol : {sig.addNameFunction(type), sig.addNamePredicate(predType)}) {
    ASS(symbol->introduced() && symbol->skip());
    ASS(!symbol->skolem());
    ASS_EQ(symbol->name().substr(0, 2), "sP");
  }
}

TEST_FUN(allSymbolKindsStoreTheirNumber)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  auto string = sig.addStringConstant("symbol_number", sort);
  auto integer = sig.addNumeralConstant(IntegerConstantType(42));
  auto rational = sig.addNumeralConstant(RationalConstantType(3, 2));
  auto real = sig.addNumeralConstant(RealConstantType(5, 2));
  auto mul = sig.addLinMul(IntegerConstantType(7));
  sig.addEquality();
  sig.getDistinctPredicate(2, sort);
  ASS_EQ(sig.getFunction(string)->number(), string);
  ASS_EQ(sig.getFunction(integer)->number(), integer);
  ASS_EQ(sig.getFunction(rational)->number(), rational);
  ASS_EQ(sig.getFunction(real)->number(), real);
  ASS_EQ(sig.getFunction(mul)->number(), mul);
  for (unsigned n = 0; n < sig.functions(); ++n) {
    ASS_EQ(sig.getFunction(n)->number(), n);
  }
  for (unsigned n = 0; n < sig.predicates(); ++n) {
    ASS_EQ(sig.getPredicate(n)->number(), n);
  }
  for (unsigned n = 0; n < sig.typeCons(); ++n) {
    ASS_EQ(sig.getTypeCon(n)->number(), n);
  }
}
