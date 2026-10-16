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
#include <type_traits>
#include <utility>
#include "Kernel/Clause.hpp"
#include "Kernel/SymbolUsage.hpp"
#include "Kernel/Problem.hpp"
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

TEST_FUN(symbolDomains)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  unsigned first = sig.symbolCount();
  auto f = sig.addFunction("signature_test_name", OperatorType::getConstantsType(sort));
  f->markIntroduced();
  f->markSkolem();
  auto p = sig.addPredicate("signature_test_name", OperatorType::getPredicateType({}));
  p->markLabel();
  auto tc = sig.addTypeCon("signature_test_name", 0);
  ASS_EQ(f->number(), first);
  ASS_EQ(p->number(), first + 1);
  ASS_EQ(tc->number(), first + 2);
  ASS_EQ(sig.getSymbol(f->number()), f);
  ASS(f->isFunction() && f->introduced() && f->skolem());
  ASS(p->isPredicate() && p->label() && p->protectedSymbol());
  ASS(tc->isTypeCon());
  ASS_EQ(sig.addFunction("signature_test_name", f->type())->number(), f->number());
  ASS_EQ(sig.addPredicate("signature_test_name", p->type())->number(), p->number());
  ASS_EQ(sig.addTypeCon("signature_test_name", 0)->number(), tc->number());

  // Boolean-valued functions belong to the function domain, not the predicate domain.
  auto b = sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::boolSort()), "bool_fun");
  ASS(b->isFunction());
  ASS(!b->isPredicate());
  auto fresh = sig.addFreshPredicate(OperatorType::getPredicateType({}), "answer");
  fresh->markAnswerPredicate();
  ASS(fresh->introduced() && fresh->skip() && fresh->answerPredicate());
}

TEST_FUN(symbolRangeSurvivesRegistration)
{
  auto& sig = *env.signature;
  auto type = OperatorType::getConstantsType(AtomicSort::defaultSort());
  sig.addFreshFunction(type, "before");
  auto symbols = sig.functionSymbols();
  unsigned count = 0;
  for (unsigned id : symbols) {
    ASS(sig.getSymbol(id)->isFunction());
    // Force the ID list to reallocate while iterating a snapshot.
    for (unsigned j = 0; j < 100; ++j) sig.addFreshFunction(type, "during");
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
  auto f = sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "sine_f");
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({}), "sine_p");
  auto s = sig.addFreshTypeCon(0, "sine_s");
  Shell::SineSymbolExtractor extractor;
  for (unsigned id : {f->number(), p->number(), s->number()}) {
    bool pred;
    unsigned decoded;
    extractor.decodeSymId(id, pred, decoded);
    ASS_EQ(decoded, id);
    ASS_EQ(pred, id == p->number());
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
  unsigned s = sig.addTypeCon("signature_print_sort", 0)->number();
  auto sort = TermList(AtomicSort::createConstant(s));
  auto p = sig.addPredicate("signature_print_pred", OperatorType::getPredicateType({sort}));
  auto f = sig.addFunction("signature_print_fun", OperatorType::getConstantsType(sort));
  auto term = TermList(Term::createConstant(f->number()));
  Indexing::LiteralCodeTree<SignatureLiteralData> tree;
  tree.insert(new SignatureLiteralData{Literal::create1(p->number(), false, term)});
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
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({}), "dense_p");
  for (unsigned i = 0; i < 1000; ++i) {
    auto f = sig.addFreshFunction(type, "dense_f");
    ASS_EQ(sig.functionIndex(f->number()), functions + i);
  }
  auto tc = sig.addFreshTypeCon(0, "dense_s");
  auto q = sig.addFreshPredicate(OperatorType::getPredicateType({}), "dense_q");
  ASS_EQ(sig.predicateIndex(0), 0u);
  ASS_EQ(sig.predicateIndex(p->number()), predicates);
  ASS_EQ(sig.predicateIndex(q->number()), predicates + 1);
  ASS_EQ(sig.typeConIndex(tc->number()), typeCons);
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
  auto f = sig.addFreshFunction(type, "prec_f");
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "prec_p");
  auto s = sig.addFreshTypeCon(0, "prec_s");
  auto g = sig.addFreshFunction(type, "prec_g");
  auto q = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "prec_q");
  auto t = sig.addFreshTypeCon(0, "prec_t");
  auto prec = [](unsigned size) { return DArray<int>::fromIterator(range(0u, size)); };
  auto fp = prec(sig.functionCount());
  auto pp = prec(sig.predicateCount());
  auto tp = prec(sig.typeConCount());
  std::swap(fp[sig.functionIndex(f->number())], fp[sig.functionIndex(g->number())]);
  InspectableLPO order(fp, tp, pp, PrecedenceOrdering::testLevels(), false);
  ASS_EQ(order.precedenceSlots(), sig.symbolCount());
  ASS_EQ(order.levelSlots(), sig.predicateCount());
  ASS_EQ(order.compareFunctionPrecedences(f->number(), g->number()), Ordering::GREATER);
  ASS_EQ(order.comparePredicatePrecedences(p->number(), q->number()), Ordering::LESS);
  ASS_EQ(order.compareTypeConPrecedences(s->number(), t->number()), Ordering::LESS);
  ASS_EQ(order.predicateLevel(0), PredLevels::EQ);

  auto weights = KboWeightMap<FuncSigTraits>::dflt(false);
  weights._introducedSymbolWeight = 7;
  ASS_EQ(weights._weights.size(), sig.functionCount());
  ASS_EQ(weights.symbolWeight(f->number()), 1u);
  auto late = sig.addFreshFunction(type, "prec_late_f");
  auto latePred = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "prec_late_p");
  auto lateType = sig.addFreshTypeCon(0, "prec_late_s");
  auto expected = env.options->introducedSymbolPrecedence() == Shell::Options::IntroducedSymbolPrecedence::BOTTOM
    ? Ordering::LESS : Ordering::GREATER;
  ASS_EQ(order.compareFunctionPrecedences(late->number(), f->number()), expected);
  ASS_EQ(order.comparePredicatePrecedences(latePred->number(), p->number()), expected);
  ASS_EQ(order.compareTypeConPrecedences(lateType->number(), s->number()), expected);
  ASS_EQ(weights.symbolWeight(late->number()), 7u);

  Shell::SymCounter counter(sig);
  auto term = TermList(Term::createConstant(f->number()));
  counter.count(Literal::create1(p->number(), true, term), 1, 1);
  ASS_EQ(counter.getPred(p->number()).pocc(), 1);
  ASS_EQ(counter.getPred(q->number()).pocc(), 0);
  ASS_EQ(counter.getFun(f->number()).occ(), 1);
  ASS_EQ(counter.getFun(g->number()).occ(), 0);
}

TEST_FUN(finiteModelUsesInterleavedSymbolOffsets)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  auto a = sig.addFreshFunction(OperatorType::getConstantsType(sort), "model_a");
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "model_p");
  auto f = sig.addFreshFunction(OperatorType::getFunctionType({sort}, sort), "model_f");
  auto q = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "model_q");
  sig.addFreshTypeCon(0, "model_s");
  auto sizes = DArray<unsigned>::initialized(sig.symbolCount(), 2);
  FMB::FiniteModelMultiSorted model(std::move(sizes));
  DArray<unsigned> noArgs;
  auto args = DArray<unsigned>::initialized(1, 2);
  model.addFunctionDefinition(a->number(), noArgs, 2);
  model.addFunctionDefinition(f->number(), args, 1);
  model.addPredicateDefinition(p->number(), args, true);
  model.addPredicateDefinition(q->number(), args, false);
  auto term = Term::createConstant(a->number());
  ASS_EQ(model.evaluateGroundTerm(term), 2u);
  ASS_EQ(model.evaluateGroundTerm(Term::create1(f->number(), TermList(term))), 1u);
  ASS(model.evaluateGroundLiteral(Literal::create1(p->number(), true, TermList(term))));
  ASS(!model.evaluateGroundLiteral(Literal::create1(q->number(), true, TermList(term))));
}

TEST_FUN(propertyScanTracksInterleavedSorts)
{
  auto& sig = *env.signature;
  sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "unused_usage_f");
  auto tc = sig.addFreshTypeCon(0, "usage_s");
  auto sort = TermList(AtomicSort::createConstant(tc->number()));
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({sort}), "usage_p");
  auto f = sig.addFreshFunction(OperatorType::getConstantsType(sort), "usage_f");
  auto clause = Clause::fromLiterals({
    Literal::create1(p->number(), true, TermList(Term::createConstant(f->number())))
  }, Inference(FromInput(UnitInputType::CONJECTURE)));
  UnitList* units = nullptr;
  UnitList::push(clause, units);

  auto first = Shell::Property::scan(units);
  auto second = Shell::Property::scan(units);
  auto empty = Shell::Property::scan(UnitList::empty());
  ASS(first->usesSort(tc->number()));
  ASS(second->usesSort(tc->number()));
  ASS(!empty->usesSort(tc->number()));
  delete first;
  delete second;
  delete empty;
  UnitList::destroy(units);
}

TEST_FUN(symbolUsageUsesDenseCategoryIndices)
{
  auto& sig = *env.signature;
  auto f = sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "count_f")->number();
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({AtomicSort::defaultSort(), AtomicSort::defaultSort()}, 1), "count_p")->number();
  auto tc = sig.addFreshTypeCon(0, "count_s")->number();
  auto unused = sig.addFreshFunction(OperatorType::getConstantsType(AtomicSort::defaultSort()), "unused_f")->number();
  auto sort = TermList(AtomicSort::createConstant(tc));
  auto term = TermList(Term::createConstant(f));
  TermList args[] = {sort, term, term};
  auto clause = Clause::fromLiterals({Literal::create(p, 3, true, args)},
      Inference(FromInput(UnitInputType::AXIOM)));
  ClauseStack clauses;
  clauses.push(clause);

  SymbolCounts counts;
  counts.countIn(pvi(ClauseStack::Iterator(clauses)));
  ASS_EQ(counts.functions.size(), sig.functionCount());
  ASS_EQ(counts.predicates.size(), sig.predicateCount());
  ASS_EQ(counts.typeCons.size(), sig.typeConCount());
  ASS_EQ(counts.functions[sig.functionIndex(f)], 2u);
  ASS_EQ(counts.functions[sig.functionIndex(unused)], 0u);
  ASS_EQ(counts.predicates[sig.predicateIndex(p)], 1u);
  ASS_EQ(counts.predicates[sig.predicateIndex(0)], 0u);
  ASS_EQ(counts.typeCons[sig.typeConIndex(tc)], 1u);

  DArray<bool> usedFunctions, usedPredicates;
  collectUsedSymbols(pvi(ClauseStack::Iterator(clauses)), usedFunctions, usedPredicates);
  ASS_EQ(usedFunctions.size(), sig.functionCount());
  ASS_EQ(usedPredicates.size(), sig.predicateCount());
  ASS(usedFunctions[sig.functionIndex(f)]);
  ASS(!usedFunctions[sig.functionIndex(unused)]);
  ASS(usedPredicates[sig.predicateIndex(p)]);
  ASS(!usedPredicates[sig.predicateIndex(0)]);

  auto late = sig.addFreshPredicate(OperatorType::getPredicateType({}), "late_count_p")->number();
  ASS_EQ(sig.predicateIndex(late), usedPredicates.size());
  clauses.reset();
  counts.countIn(pvi(ClauseStack::Iterator(clauses)));
  collectUsedSymbols(pvi(ClauseStack::Iterator(clauses)), usedFunctions, usedPredicates);
  ASS_EQ(counts.functions[sig.functionIndex(f)], 0u);
  ASS_EQ(counts.predicates[sig.predicateIndex(p)], 0u);
  ASS_EQ(counts.typeCons[sig.typeConIndex(tc)], 0u);
  ASS(!usedFunctions[sig.functionIndex(f)]);
  ASS(!usedPredicates[sig.predicateIndex(p)]);
  ASS(!usedPredicates[sig.predicateIndex(late)]);
}

namespace {
class InspectableKBO : public KBO {
public:
  using KBO::KBO;
  using KBO::symbolWeight;
};
}

TEST_FUN(kboGeneratedWeightsUseDenseCategoryIndices)
{
  auto& sig = *env.signature;
  auto sort = AtomicSort::defaultSort();
  auto f = sig.addFreshFunction(OperatorType::getConstantsType(sort), "weight_f")->number();
  auto p = sig.addFreshPredicate(OperatorType::getPredicateType({sort, sort, sort}), "weight_p")->number();
  sig.addFreshTypeCon(0, "weight_s")->number();
  auto g = sig.addFreshFunction(OperatorType::getConstantsType(sort), "weight_g")->number();
  auto ft = Term::createConstant(f);
  auto gt = Term::createConstant(g);
  TermList args[] = {TermList(ft), TermList(ft), TermList(gt)};
  auto clause = Clause::fromLiterals({Literal::create(p, 3, true, args)},
      Inference(FromInput(UnitInputType::AXIOM)));
  UnitList* units = nullptr;
  UnitList::push(clause, units);
  Problem prb(units);
  Shell::Options opts;
  opts.set("symbol_precedence", "occurrence");
  opts.set("kbo_weight_scheme", "precedence");
  InspectableKBO precedence(prb, opts);
  ASS_EQ(precedence.symbolWeight(ft), static_cast<int>(sig.functionIndex(f) + 1));
  ASS_EQ(precedence.symbolWeight(gt), static_cast<int>(sig.functionIndex(g) + 1));

  opts.set("kbo_weight_scheme", "inv_precedence");
  InspectableKBO inversePrecedence(prb, opts);
  ASS_EQ(inversePrecedence.symbolWeight(ft), static_cast<int>(sig.functionCount() - sig.functionIndex(f)));
  ASS_EQ(inversePrecedence.symbolWeight(gt), static_cast<int>(sig.functionCount() - sig.functionIndex(g)));

  opts.set("kbo_weight_scheme", "frequency");
  InspectableKBO frequency(prb, opts);
  ASS_EQ(frequency.symbolWeight(ft), 2);
  ASS_EQ(frequency.symbolWeight(gt), 1);

  opts.set("kbo_weight_scheme", "inv_frequency");
  InspectableKBO inverseFrequency(prb, opts);
  ASS_EQ(inverseFrequency.symbolWeight(ft), 1);
  ASS_EQ(inverseFrequency.symbolWeight(gt), 2);
}

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
  auto functions = sig.functionCount();
  auto predicates = sig.predicateCount();
  sig.protectFunction(f->number());
  sig.markAnswerPredicate(p->number());
  ASS(f->introduced() && f->protectedSymbol());
  ASS(p->introduced() && p->answerPredicate() && p->protectedSymbol());
  ASS_EQ(sig.getFunction(f->number()), f);
  ASS_EQ(sig.getPredicate(p->number()), p);
  ASS_EQ(sig.functionCount(), functions);
  ASS_EQ(sig.predicateCount(), predicates);
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
  for (unsigned n : sig.functionSymbols()) {
    ASS_EQ(sig.getFunction(n)->number(), n);
  }
  for (unsigned n : sig.predicateSymbols()) {
    ASS_EQ(sig.getPredicate(n)->number(), n);
  }
  for (unsigned n : sig.typeConSymbols()) {
    ASS_EQ(sig.getTypeCon(n)->number(), n);
  }
}
