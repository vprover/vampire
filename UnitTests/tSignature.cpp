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
#include "Kernel/Clause.hpp"
#include "Shell/Property.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/KBO.hpp"
#include "Kernel/LPO.hpp"
#include "Shell/SymCounter.hpp"
#include "FMB/FiniteModelMultiSorted.hpp"
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

TEST_FUN(categoryIndicesStayDenseAcrossRegistration)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  unsigned functions = sig.functionCount();
  unsigned predicates = sig.predicateCount();
  unsigned typeCons = sig.typeConCount();
  auto p = sig.freshPredicate(OperatorType::getPredicateType({}), "dense_p");
  for (unsigned i = 0; i < 1000; ++i) {
    auto f = sig.freshFunction(type, "dense_f");
    ASS_EQ(sig.functionIndex(f.number()), functions + i);
  }
  auto tc = sig.freshTypeConstructor(0, "dense_s");
  auto q = sig.freshPredicate(OperatorType::getPredicateType({}), "dense_q");
  ASS_EQ(sig.predicateIndex(0), 0u);
  ASS_EQ(sig.predicateIndex(p.number()), predicates);
  ASS_EQ(sig.predicateIndex(q.number()), predicates + 1);
  ASS_EQ(sig.typeConIndex(tc.number()), typeCons);
  ASS_EQ(sig.predicateCount(), predicates + 2);
  for (auto ids : {sig.functionSymbols(), sig.predicateSymbols(), sig.typeConSymbols()}) {
    for (unsigned i = 0; i < ids.size(); ++i)
      ASS_EQ(sig.getSymbol(ids[i])->categoryIndex(), i);
  }
}

namespace {
class InspectableLPO : public LPO {
public:
  using LPO::LPO;
  using PrecedenceOrdering::compareFunctionPrecedences;
  using PrecedenceOrdering::compareTypeConPrecedences;
  using PrecedenceOrdering::predicateLevel;
  unsigned precedenceSlots() const { return _symbolPrecedences.size(); }
  unsigned levelSlots() const { return _predicateLevels.size(); }
};
}

TEST_FUN(precedenceStorageHandlesInterleavedAndLateSymbols)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  auto type = OperatorType::getConstantsType(sort);
  auto f = sig.freshFunction(type, "prec_f");
  auto p = sig.freshPredicate(OperatorType::getPredicateType({sort}), "prec_p");
  auto s = sig.freshTypeConstructor(0, "prec_s");
  auto g = sig.freshFunction(type, "prec_g");
  auto q = sig.freshPredicate(OperatorType::getPredicateType({sort}), "prec_q");
  auto t = sig.freshTypeConstructor(0, "prec_t");
  auto prec = [](unsigned size) { return DArray<int>::fromIterator(range(0u, size)); };
  auto fp = prec(sig.functionCount());
  auto pp = prec(sig.predicateCount());
  auto tp = prec(sig.typeConCount());
  std::swap(fp[sig.functionIndex(f.number())], fp[sig.functionIndex(g.number())]);
  InspectableLPO order(fp, tp, pp, PrecedenceOrdering::testLevels(), false);
  ASS_EQ(order.precedenceSlots(), sig.symbolCount());
  ASS_EQ(order.levelSlots(), sig.predicateCount());
  ASS_EQ(order.compareFunctionPrecedences(f.number(), g.number()), Ordering::GREATER);
  ASS_EQ(order.comparePredicatePrecedences(p.number(), q.number()), Ordering::LESS);
  ASS_EQ(order.compareTypeConPrecedences(s.number(), t.number()), Ordering::LESS);
  ASS_EQ(order.predicateLevel(0), PredLevels::EQ);

  auto weights = KboWeightMap<FuncSigTraits>::dflt(false);
  weights._introducedSymbolWeight = 7;
  ASS_EQ(weights._weights.size(), sig.functionCount());
  ASS_EQ(weights.symbolWeight(f.number()), 1u);
  auto late = sig.freshFunction(type, "prec_late_f");
  auto latePred = sig.freshPredicate(OperatorType::getPredicateType({sort}), "prec_late_p");
  auto lateType = sig.freshTypeConstructor(0, "prec_late_s");
  auto expected = env.options->introducedSymbolPrecedence() == Shell::Options::IntroducedSymbolPrecedence::BOTTOM
    ? Ordering::LESS : Ordering::GREATER;
  ASS_EQ(order.compareFunctionPrecedences(late.number(), f.number()), expected);
  ASS_EQ(order.comparePredicatePrecedences(latePred.number(), p.number()), expected);
  ASS_EQ(order.compareTypeConPrecedences(lateType.number(), s.number()), expected);
  ASS_EQ(weights.symbolWeight(late.number()), 7u);

  Shell::SymCounter counter(sig);
  auto term = TermList(Term::createConstant(f.number()));
  counter.count(Literal::create1(p.number(), true, term), 1, 1);
  ASS_EQ(counter.getPred(p.number()).pocc(), 1);
  ASS_EQ(counter.getPred(q.number()).pocc(), 0);
  ASS_EQ(counter.getFun(f.number()).occ(), 1);
  ASS_EQ(counter.getFun(g.number()).occ(), 0);
}

TEST_FUN(finiteModelUsesInterleavedSymbolOffsets)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  auto a = sig.freshFunction(OperatorType::getConstantsType(sort), "model_a");
  auto p = sig.freshPredicate(OperatorType::getPredicateType({sort}), "model_p");
  auto f = sig.freshFunction(OperatorType::getFunctionType({sort}, sort), "model_f");
  auto q = sig.freshPredicate(OperatorType::getPredicateType({sort}), "model_q");
  sig.freshTypeConstructor(0, "model_s");
  auto sizes = DArray<unsigned>::initialized(sig.symbolCount(), 2);
  FMB::FiniteModelMultiSorted model(std::move(sizes));
  DArray<unsigned> noArgs;
  auto args = DArray<unsigned>::initialized(1, 2);
  model.addFunctionDefinition(a.number(), noArgs, 2);
  model.addFunctionDefinition(f.number(), args, 1);
  model.addPredicateDefinition(p.number(), args, true);
  model.addPredicateDefinition(q.number(), args, false);
  auto term = Term::createConstant(a.number());
  ASS_EQ(model.evaluateGroundTerm(term), 2u);
  ASS_EQ(model.evaluateGroundTerm(Term::create1(f.number(), TermList(term))), 1u);
  ASS(model.evaluateGroundLiteral(Literal::create1(p.number(), true, TermList(term))));
  ASS(!model.evaluateGroundLiteral(Literal::create1(q.number(), true, TermList(term))));
}

TEST_FUN(propertyScanCountsAndResetsInterleavedSymbols)
{
  auto& sig = *env.signature;
  auto f = sig.freshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "usage_f");
  auto p = sig.freshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort()}, 1), "usage_p");
  auto tc = sig.freshTypeConstructor(0, "usage_s");
  auto sort = TermList(AtomicSort::createConstant(tc.number()));
  auto clause = Clause::fromLiterals({
    Literal::create2(p.number(), true, sort, TermList(Term::createConstant(f.number())))
  }, Inference(FromInput(UnitInputType::ASSUMPTION)));
  UnitList* units = nullptr;
  UnitList::push(clause, units);

  delete Shell::Property::scan(units);
  ASS_EQ(f->usageCnt(), 1u);
  ASS_EQ(p->usageCnt(), 1u);
  ASS_EQ(tc->usageCnt(), 1u);

  // Rescanning must not accumulate counts from the previous scan.
  delete Shell::Property::scan(units);
  ASS_EQ(f->usageCnt(), 1u);
  ASS_EQ(p->usageCnt(), 1u);
  ASS_EQ(tc->usageCnt(), 1u);

  delete Shell::Property::scan(UnitList::empty());
  ASS_EQ(f->usageCnt(), 0u);
  ASS_EQ(p->usageCnt(), 0u);
  ASS_EQ(tc->usageCnt(), 0u);
  UnitList::destroy(units);
}
