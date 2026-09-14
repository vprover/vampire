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
#include "Kernel/NumTraits.hpp"
#include "Shell/SineUtils.hpp"
#include "Indexing/LiteralCodeTree.hpp"
#include <sstream>

using namespace Kernel;
using namespace Lib;

TEST_FUN(symbolDomainsAndBuilders)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  unsigned first = sig.symbolCount();
  auto f = sig.function("signature_test_name", OperatorType::getConstantsType(sort)).introduced().skolem();
  auto p = sig.predicate("signature_test_name", OperatorType::getPredicateType({})).label();
  auto tc = sig.typeConstructor("signature_test_name", 0);
  ASS_EQ(f.number(), first);
  ASS_EQ(p.number(), first + 1);
  ASS_EQ(tc.number(), first + 2);
  ASS_EQ(sig.getSymbol(f.number()), &f.symbol());
  ASS(f->isFunction() && f->introduced() && f->skolem());
  ASS(p->isPredicate() && p->label() && p->protectedSymbol());
  ASS(tc->isTypeCon());
  ASS_EQ(sig.function("signature_test_name", f->type()).number(), f.number());
  ASS_EQ(sig.predicate("signature_test_name", p->type()).number(), p.number());
  ASS_EQ(sig.typeConstructor("signature_test_name", 0).number(), tc.number());

  // Boolean-valued functions belong to the function domain, not the predicate domain.
  auto b = sig.freshFunction(OperatorType::getConstantsType(AtomicSort::boolSort()), "bool_fun");
  ASS(b->isFunction());
  ASS(!b->isPredicate());
  auto fresh = sig.freshPredicate(OperatorType::getPredicateType({}), "answer").answerPredicate();
  ASS(fresh->introduced() && fresh->skip() && fresh->answerPredicate());
}

TEST_FUN(symbolRangeSurvivesRegistration)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  sig.freshFunction(type, "before");
  auto symbols = sig.functionSymbols();
  unsigned count = 0;
  for (unsigned id : symbols) {
    ASS(sig.getSymbol(id)->isFunction());
    // Force the ID list to reallocate while iterating a snapshot.
    for (unsigned j = 0; j < 100; ++j) sig.freshFunction(type, "during");
    ++count;
  }
  ASS_EQ(count, symbols.size());
  ASS_EQ(sig.functionSymbols().size(), symbols.size() * 101);
}

TEST_FUN(builtinsAndArithmeticHaveUniqueIds)
{
  auto& sig = *env.signature;
  ASS(sig.getSymbol(0)->isPredicate());
  ASS_EQ(sig.symbolName(0), "=");
  ASS_EQ(AtomicSort::defaultSort().term()->functor(), Signature::DEFAULT_SORT_CON);
  ASS_EQ(AtomicSort::boolSort().term()->functor(), Signature::BOOL_SRT_CON);
  ASS_EQ(AtomicSort::intSort().term()->functor(), Signature::INTEGER_SRT_CON);
  ASS_EQ(AtomicSort::realSort().term()->functor(), Signature::REAL_SRT_CON);
  ASS_EQ(AtomicSort::rationalSort().term()->functor(), Signature::RATIONAL_SRT_CON);
  auto minus = RatTraits::linMulF(RationalConstantType(-1));
  auto numeral = RatTraits::numeralF(RationalConstantType(-1));
  ASS_NEQ(minus, numeral);
  ASS(sig.getSymbol(minus)->linMul());
  ASS_EQ(sig.getSymbol(minus)->arity(), 1);
  ASS_EQ(sig.getSymbol(numeral)->arity(), 0);
  unsigned count = 0;
  for (auto ids : {sig.functionSymbols(), sig.predicateSymbols(), sig.typeConSymbols()}) {
    for (unsigned id : ids) { ASS_EQ(sig.getSymbol(id)->number(), id); ++count; }
  }
  ASS_EQ(count, sig.symbolCount());
}

TEST_FUN(sineUsesSignatureIds)
{
  auto& sig = *env.signature;
  auto f = sig.freshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "sine_f");
  auto p = sig.freshPredicate(OperatorType::getPredicateType({}), "sine_p");
  auto s = sig.freshTypeConstructor(0, "sine_s");
  Shell::SineSymbolExtractor extractor;
  for (unsigned id : {f.number(), p.number(), s.number()}) {
    bool pred;
    unsigned decoded;
    extractor.decodeSymId(id, pred, decoded);
    ASS_EQ(decoded, id);
    ASS_EQ(pred, id == p.number());
    ASS(extractor.validSymId(id));
  }
  ASS_EQ(extractor.getSymIdBound(), sig.symbolCount());
  ASS(!extractor.validSymId(sig.symbolCount()));
}

namespace {
struct SignatureLiteralData {
  Literal* literal;
  Literal* key() const { return literal; }
  friend std::ostream& operator<<(std::ostream& out, const SignatureLiteralData&) { return out << "entry"; }
};
}

TEST_FUN(codeTreePrintsGlobalSymbolNames)
{
  auto& sig = *env.signature;
  unsigned s = sig.typeConstructor("signature_print_sort", 0).number();
  auto sort = TermList(AtomicSort::createConstant(s));
  auto p = sig.predicate("signature_print_pred", OperatorType::getPredicateType({sort}));
  auto f = sig.function("signature_print_fun", OperatorType::getConstantsType(sort));
  auto term = TermList(Term::createConstant(f.number()));
  Indexing::LiteralCodeTree<SignatureLiteralData> tree;
  tree.insert(new SignatureLiteralData{Literal::create1(p.number(), false, term)});
  std::ostringstream output;
  output << tree;
  ASS_NEQ(output.str().find("~signature_print_pred"), std::string::npos);
  ASS_NEQ(output.str().find("signature_print_fun"), std::string::npos);

  Indexing::LiteralCodeTree<SignatureLiteralData> equalityTree;
  equalityTree.insert(new SignatureLiteralData{Literal::createEquality(true, TermList::var(0), TermList::var(1), sort)});
  std::ostringstream equalityOutput;
  equalityOutput << equalityTree;
  ASS_NEQ(equalityOutput.str().find("signature_print_sort"), std::string::npos);
}
