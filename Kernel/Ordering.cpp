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
 * @file Ordering.cpp
 * Implements class Ordering.
 */

#include <fstream>

#include "Forwards.hpp"

#include "Indexing/TermSharing.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"

#include "Shell/Options.hpp"
#include "Shell/Property.hpp"

#include "LPO.hpp"
#include "KBO.hpp"
#include "SKIKBO.hpp"
#include "KBOForEPR.hpp"
#include "Problem.hpp"
#include "Signature.hpp"
#include "Kernel/NumTraits.hpp" 
#include "Kernel/LaLpo.hpp"
#include "Kernel/QKbo.hpp"

#include "Ordering.hpp"

#define NONINTERPRETED_PRECEDENCE_BOOST 0x1000

#define NONINTERPRETED_LEVEL_BOOST 0x1000
#define COLORED_LEVEL_BOOST 0x10000

using namespace Lib;
using namespace Kernel;

OrderingSP Ordering::s_globalOrdering;

Ordering::Ordering() : _eqCmp(unique_ptr<EqCmp>(new  EqCmp()))
{
  CALL("Ordering::Ordering");
}

Ordering::~Ordering()
{
  CALL("Ordering::~Ordering");
}


/**
 * If there is no global ordering yet, assign @c ordering to be
 * it and return true. Otherwise return false.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
bool Ordering::trySetGlobalOrdering(OrderingSP ordering)
{
  CALL("Ordering::trySetGlobalOrdering");

  if(s_globalOrdering) {
    return false;
  }
  s_globalOrdering = ordering;
  return true;
}

/**
 * If global ordering is set, return pointer to it, otherwise
 * return 0.
 *
 * We store orientation of equalities in global ordering inside
 * the term sharing structure. Setting an ordering to be global
 * does not change the behavior of Vampire, but may lead to
 * better performance, as the equality orientation will be cached
 * inside the sharing structure.
 */
Ordering* Ordering::tryGetGlobalOrdering()
{
  CALL("Ordering::tryGetGlobalOrdering");

  if(s_globalOrdering) {
    return s_globalOrdering.ptr();
  }
  else {
    return 0;
  }
}

/**
 * Creates the ordering
 *
 * Currently the ordering is created in @b SaturationAlgorithm::createFromOptions()
 */
Ordering* Ordering::create(Problem& prb, const Options& opt)
{
  CALL("Ordering::create");

  if(env.options->combinatorySup() || env.options->lambdaFreeHol()){
    return new SKIKBO(prb, opt, env.options->lambdaFreeHol());
  }

  Ordering* out;
  switch (env.options->termOrdering()) {
  case Options::TermOrdering::KBO:
    // KBOForEPR does not support 
    // - colors
    // - user specified symbol weights
    // TODO fix this! 
    if(prb.getProperty()->maxFunArity()==0 
        && prb.getProperty()->maxTypeConArity() == 0
        && !env.colorUsed
        && env.options->predicateWeights() == ""
        && env.options->functionWeights() == ""
        && env.options->kboWeightGenerationScheme() == Options::KboWeightGenerationScheme::CONST
        && !env.options->kboMaxZero()
        && !prb.hasInterpretedOperations()
        ) {
      out = new KBOForEPR(prb, opt);
    } else {
      out = new KBO(prb, opt);
    }
    break;
  case Options::TermOrdering::LALPO:
    out = new LaLpo(prb, opt);
    break;
  case Options::TermOrdering::QKBO:
    out = new QKbo(prb, opt);
    break;
  case Options::TermOrdering::LPO:
    out = new LPO(prb, opt);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  //TODO currently do not show SKIKBO
  if (opt.showSimplOrdering()) {
    env.beginOutput();
    out->show(env.out());
    env.endOutput();
  }
  return out;
}


Ordering::Result Ordering::fromComparison(Comparison c)
{
  CALL("Ordering::fromComparison");

  switch(c) {
  case Lib::GREATER:
    return GREATER;
  case Lib::EQUAL:
    return EQUAL;
  case Lib::LESS:
    return LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

Comparison Ordering::intoComparison(Ordering::Result r)
{
  CALL("Ordering::intoComparison");

  switch(r) {
  case Ordering::Result::GREATER: return Lib::GREATER;
  case Ordering::Result::EQUAL:   return Lib::EQUAL;
  case Ordering::Result::LESS:    return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

const char* Ordering::resultToString(Result r)
{
  CALL("Ordering::resultToString");

  switch(r) {
  case GREATER:
    return "GREATER";
  case GREATER_EQ:
    return "GREATER_EQ";
  case LESS:
    return "LESS";
  case LESS_EQ:
    return "LESS_EQ";
  case EQUAL:
    return "EQUAL";
  case INCOMPARABLE:
    return "INCOMPARABLE";
  default:
    ASSERTION_VIOLATION;
    return 0;
  }
}

/**
 * Remove non-maximal literals from the list @b lits. The order
 * of remaining literals stays unchanged.
 */
void Ordering::removeNonMaximal(LiteralList*& lits) const
{
  CALL("Ordering::removeNonMaximal");

  LiteralList** ptr1=&lits;
  while(*ptr1) {
    LiteralList** ptr2=&(*ptr1)->tailReference();
    while(*ptr2 && *ptr1) {
      Ordering::Result res=compare((*ptr1)->head(), (*ptr2)->head());

      if(res==Ordering::GREATER || res==Ordering::GREATER_EQ || res==Ordering::EQUAL) {
	LiteralList::pop(*ptr2);
	continue;
      } else if(res==Ordering::LESS || res==Ordering::LESS_EQ) {
	LiteralList::pop(*ptr1);
	goto topLevelContinue;
      }
      ptr2=&(*ptr2)->tailReference();
    }
    ptr1=&(*ptr1)->tailReference();
topLevelContinue: ;
  }

}

Ordering::Result Ordering::getEqualityArgumentOrder(Literal* eq) const
{
  CALL("Ordering::getEqualityArgumentOrder");
  ASS(eq->isEquality());

  if(tryGetGlobalOrdering()!=this) {
    return compare(*eq->nthArgument(0), *eq->nthArgument(1));
  }

  Result res;
  ArgumentOrderVals precomputed = static_cast<ArgumentOrderVals>(eq->getArgumentOrderValue());
  if(precomputed!=AO_UNKNOWN) {
    res = static_cast<Result>(precomputed);
    ASS_EQ(res, compare(*eq->nthArgument(0), *eq->nthArgument(1)));
  }
  else {
    res = compare(*eq->nthArgument(0), *eq->nthArgument(1));
    eq->setArgumentOrderValue(static_cast<ArgumentOrderVals>(res));
  }
  return res;
}

//////////////////////////////////////////////////
// PrecedenceOrdering class
//////////////////////////////////////////////////

Ordering::Result PrecedenceOrdering::compare(Literal* l1, Literal* l2) const
{
  CALL("PrecedenceOrdering::compare(Literal*...)");

  ASS(l1->shared());
  ASS(l2->shared());

  if (l1 == l2) {
    return EQUAL;
  }

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if( (l1->isNegative() ^ l2->isNegative()) && (p1==p2) &&
	  l1->weight()==l2->weight() && l1->numVarOccs()==l2->numVarOccs() &&  //this line is just optimization, so we don't check whether literals are opposite when they cannot be
	  l1==env.sharing->tryGetOpposite(l2)) {
    return l1->isNegative() ? LESS : GREATER;
  }

  if (p1 != p2) {
    Comparison levComp=Int::compare(predicateLevel(p1),predicateLevel(p2));
    if(levComp!=Lib::EQUAL) {
      return fromComparison(levComp);
    }
  }

  if(l1->isEquality()) {
    ASS(l2->isEquality())
    return compareEqualities(l1, l2);
  }

  if(_reverseLCM && (l1->isNegative() || l2->isNegative()) ) {
    if(l1->isNegative() && l2->isNegative()) {
      return reverse(comparePredicates(l1, l2));
    }
    else {
      return l1->isNegative() ? LESS : GREATER;
    }
  }
  return comparePredicates(l1, l2);
} // PrecedenceOrdering::compare()

/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality). If a predicate is colored, its level is multiplied by
 * the COLORED_LEVEL_BOOST value.
 */
int PrecedenceOrdering::predicateLevel (unsigned pred) const
{
  int basic=pred >= _predicates ? 1 : _predicateLevels[pred];
  if(NONINTERPRETED_LEVEL_BOOST && !env.signature->getPredicate(pred)->interpreted()) {
    ASS(!Signature::isEqualityPredicate(pred)); //equality is always interpreted
    basic+=NONINTERPRETED_LEVEL_BOOST;
  }
  if(env.signature->predicateColored(pred)) {
    ASS_NEQ(pred,0); //equality should never be colored
    return COLORED_LEVEL_BOOST*basic;
  } else {
    return basic;
  }
} // PrecedenceOrdering::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 */
int PrecedenceOrdering::predicatePrecedence (unsigned pred) const
{
  int res=pred >= _predicates ? (int)pred : _predicatePrecedences[pred];
  if(NONINTERPRETED_PRECEDENCE_BOOST) {
    ASS_EQ(NONINTERPRETED_PRECEDENCE_BOOST & 1, 0); // an even number

    bool intp = env.signature->getPredicate(pred)->interpreted();
    res *= 2;
    return intp ? res+1 : res+NONINTERPRETED_PRECEDENCE_BOOST;
  }
  return res;
} // PrecedenceOrdering::predicatePrecedences

Comparison PrecedenceOrdering::compareFunctors(unsigned fun1, unsigned fun2) const
{
  CALL("PrecedenceOrdering::compareFunctors");

  if(fun1==fun2) {
    return Lib::EQUAL;
  }
  switch(compareFunctionPrecedences(fun1, fun2)) {
  case GREATER: return Lib::GREATER;
  case LESS: return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Compare precedences of two function symbols
 */ //TODO update for HOL>?
Ordering::Result PrecedenceOrdering::compareFunctionPrecedences(unsigned fun1, unsigned fun2) const
{
  CALL("PrecedenceOrdering::compareFunctionPrecedences");

  if (fun1 == fun2)
    return EQUAL;

  if (_qkboPrecedence) {

    // one is less than everything else
    if (fun1 == IntTraits::oneF()) { return LESS; }
    if (fun1 == RatTraits::oneF()) { return LESS; }
    if (fun1 == RealTraits::oneF()) { return LESS; }

    if (fun2 == IntTraits::oneF()) { return GREATER; } 
    if (fun2 == RatTraits::oneF()) { return GREATER; }
    if (fun2 == RealTraits::oneF()) { return GREATER; }


  } else {

    // unary minus is the biggest
    if (fun1 == IntTraits::minusF()) { return GREATER; } 
    if (fun1 == RatTraits::minusF()) { return GREATER; }
    if (fun1 == RealTraits::minusF()) { return GREATER; }

    if (fun2 == IntTraits::minusF()) { return LESS; }
    if (fun2 == RatTraits::minusF()) { return LESS; }
    if (fun2 == RealTraits::minusF()) { return LESS; }

  }

  // $$false is the smallest
  if (env.signature->isFoolConstantSymbol(false,fun1)) {
    return LESS;
  }
  if (env.signature->isFoolConstantSymbol(false,fun2)) {
    return GREATER;
  }

  // $$true is the second smallest
  if (env.signature->isFoolConstantSymbol(true,fun1)) {
    return LESS;
  }

  if (env.signature->isFoolConstantSymbol(true,fun2)) {
    return GREATER;
  }

  Signature::Symbol* s1=env.signature->getFunction(fun1);
  Signature::Symbol* s2=env.signature->getFunction(fun2);
  // term algebra constructors are smaller than other symbols
  if(s1->termAlgebraCons() && !s2->termAlgebraCons()) {
    return LESS;
  }
  if(!s1->termAlgebraCons() && s2->termAlgebraCons()) {
    return GREATER;
  }
  // uninterpreted things are greater than interpreted things
  if(!s1->interpreted()) {
    if(s2->interpreted()) {
      return GREATER;
    }
    static bool reverse = env.options->introducedSymbolPrecedence() == Shell::Options::IntroducedSymbolPrecedence::BOTTOM;
    //two non-interpreted functions
    return fromComparison(Int::compare(
        fun1 >= _functions ? (int)(reverse ? -fun1 : fun1) : _functionPrecedences[fun1],
        fun2 >= _functions ? (int)(reverse ? -fun2 : fun2) : _functionPrecedences[fun2] ));
  }
  if(!s2->interpreted()) {
    return LESS;
  }
  if(s1->arity()) {
    if(!s2->arity()) {
      return GREATER;
    }
    //two interpreted functions
    return fromComparison(Int::compare(fun1, fun2));
  }
  if(s2->arity()) {
    return LESS;
  }
  //two interpreted constants

  if (!s1->interpretedNumber() || !s2->interpretedNumber()) {
    return fromComparison(Int::compare(fun1, fun2));
  }

  Comparison cmpRes;
  if(s1->integerConstant() && s2->integerConstant()) {
    cmpRes = IntegerConstantType::comparePrecedence(s1->integerValue(), s2->integerValue());
  }
  else if(s1->rationalConstant() && s2->rationalConstant()) {
    cmpRes = RationalConstantType::comparePrecedence(s1->rationalValue(), s2->rationalValue());
  }
  else if(s1->realConstant() && s2->realConstant()) {
    cmpRes = RealConstantType::comparePrecedence(s1->realValue(), s2->realValue());
  }
  else if(s1->integerConstant()) {
    ASS_REP(s2->rationalConstant() || s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->integerConstant()) {
    ASS_REP(s1->rationalConstant() || s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else if(s1->rationalConstant()) {
    ASS_REP(s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->rationalConstant()) {
    ASS_REP(s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else {
    ASSERTION_VIOLATION;
    cmpRes = Int::compare(fun1, fun2);
  }
  return fromComparison(cmpRes);
}

/**
 * Compare precedences of two type constructor symbols
 * At the moment, completely non-optimised
 */ 
Ordering::Result PrecedenceOrdering::compareTypeConPrecedences(unsigned tyc1, unsigned tyc2) const
{
  CALL("PrecedenceOrdering::compareTypeConPrecedences");

  if (tyc1 == tyc2)
    return EQUAL;

  static bool reverse = env.options->introducedSymbolPrecedence() == Shell::Options::IntroducedSymbolPrecedence::BOTTOM;

  return fromComparison(Int::compare(
      (int)(reverse ? -tyc1 : tyc1),
      (int)(reverse ? -tyc2 : tyc2)));
}

struct SymbolComparator {
  bool _forFunct;
  SymbolComparator(bool forFunct) : _forFunct(forFunct) {}

  Signature::Symbol* getSymbol(unsigned s) {
    return _forFunct ? env.signature->getFunction(s) : env.signature->getPredicate(s);
  }  
};

template<typename InnerComparator>
struct BoostWrapper : public SymbolComparator
{
  BoostWrapper(bool forFunct) : SymbolComparator(forFunct) {}

  Comparison compare(unsigned s1, unsigned s2)
  {
    static Options::SymbolPrecedenceBoost boost = env.options->symbolPrecedenceBoost();
    Comparison res = EQUAL;
    auto sym1 = getSymbol(s1);
    auto sym2 = getSymbol(s2);
    bool u1 = sym1->inUnit(); 
    bool u2 = sym2->inUnit(); 
    bool g1 = sym1->inGoal();
    bool g2 = sym2->inGoal();
    bool i1 = sym1->introduced();
    bool i2 = sym2->introduced();
    switch(boost){
      case Options::SymbolPrecedenceBoost::NONE:
        break;
      case Options::SymbolPrecedenceBoost::GOAL:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::UNIT:
        if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::GOAL_UNIT:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        else if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::NON_INTRO:
        if (i1 && !i2) { res = LESS; }
        else if (!i1 && i2) { res = GREATER; }
        break;
      case Options::SymbolPrecedenceBoost::INTRO:
        if (!i1 && i2) { res = LESS; }
        else if (i1 && !i2) { res = GREATER; }
        break;
    }
    if(res==EQUAL){
      // fallback to Inner
      res = InnerComparator(_forFunct).compare(s1,s2);
    }
    return res;
  }
};

struct OccurenceTiebreak {
  OccurenceTiebreak(bool) {} // the bool is a dummy argument, required by the template recursion convention

  Comparison compare(unsigned s1, unsigned s2) {  return Int::compare(s1,s2); }
};

template<bool revert = false, typename InnerComparator = OccurenceTiebreak>
struct FreqComparator : public SymbolComparator
{
  FreqComparator(bool forFunct) : SymbolComparator(forFunct) {}

  Comparison compare(unsigned s1, unsigned s2)
  {
    unsigned c1 = getSymbol(s1)->usageCnt();
    unsigned c2 = getSymbol(s2)->usageCnt();
    // note that we have: "rare is large" (unless reverted)
    Comparison res = revert ? Int::compare(c1,c2) : Int::compare(c2,c1);
    if(res==EQUAL){
      // fallback to Inner
      res = InnerComparator(_forFunct).compare(s1,s2);
    }
    return res;
  }
};

template<bool revert = false, typename InnerComparator = OccurenceTiebreak>
struct ArityComparator : public SymbolComparator
{
  ArityComparator(bool forFunct) : SymbolComparator(forFunct) {}

  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res= Int::compare(getSymbol(u1)->arity(),getSymbol(u2)->arity());
    if (revert) {
      res = Lib::revert(res);
    }
    if(res==EQUAL) {
      // fallback to Inner 
      res = InnerComparator(_forFunct).compare(u1,u2);
    }
    return res;
  }
};

template<int spc, bool revert = false, typename InnerComparator = OccurenceTiebreak>
struct SpecAriFirstComparator : public SymbolComparator
{
  SpecAriFirstComparator(bool forFunct) : SymbolComparator(forFunct) {}

  Comparison compare(unsigned s1, unsigned s2)
  {
    unsigned a1 = getSymbol(s1)->arity();
    unsigned a2 = getSymbol(s2)->arity();
    if (a1 == spc && a2 != spc) {
      return revert ? LESS : GREATER;
    } else if (a1 != spc && a2 == spc) {
      return revert ? GREATER : LESS;
    }
    // fallback to Inner
    return InnerComparator(_forFunct).compare(s1,s2);
  }
};

template<bool revert = false, typename InnerComparator = OccurenceTiebreak>
using UnaryFirstComparator = SpecAriFirstComparator<1,revert,InnerComparator>;

template<bool revert = false, typename InnerComparator = OccurenceTiebreak>
using ConstFirstComparator = SpecAriFirstComparator<0,revert,InnerComparator>;

static void loadPermutationFromString(DArray<unsigned>& p, const vstring& str) {
  CALL("loadPermutationFromString");

  std::stringstream ss(str.c_str());
  unsigned i = 0;
  unsigned val;
  while (ss >> val)
  {
      if (i >= p.size()) {
        break;
      }

      if (val >= p.size()) {
        break;
      }

      p[i++] = val;

      if (ss.peek() == ',')
          ss.ignore();
  }
}

bool isPermutation(const DArray<int>& xs) {
  CALL("isPermutation");
  DArray<int> cnts(xs.size()); 
  cnts.init(xs.size(), 0);
  for (unsigned i = 0; i < xs.size(); i++) {
    cnts[xs[i]] += 1;
  }
  for (unsigned i = 0; i < xs.size(); i++) {
    if (cnts[xs[i]] != 1) {
      return false;
    }
  }
  return true;
}

/**
 * Create a PrecedenceOrdering object.
 */
PrecedenceOrdering::PrecedenceOrdering(const DArray<int>& funcPrec, const DArray<int>& predPrec, const DArray<int>& predLevels, bool reverseLCM, bool qkboPrecedence)
  : _predicates(predPrec.size()),
    _functions(funcPrec.size()),
    _predicateLevels(predLevels),
    _predicatePrecedences(predPrec),
    _functionPrecedences(funcPrec),
    _reverseLCM(reverseLCM),
    _qkboPrecedence(qkboPrecedence)
{
  CALL("PrecedenceOrdering::PrecedenceOrdering(const DArray<int>&, const DArray<int>&, const DArray<int>&, bool)");
  ASS_EQ(env.signature->predicates(), _predicates);
  ASS_EQ(env.signature->functions(), _functions);
  ASS(isPermutation(_functionPrecedences))
  ASS(isPermutation(_predicatePrecedences))
  checkLevelAssumptions(predLevels);
}

/**
 * Create a PrecedenceOrdering object.
 *
 * "Intermediate" constructor; this is needed so that we only call predPrecFromOpts once (and use it here twice).
 */
PrecedenceOrdering::PrecedenceOrdering(Problem& prb, const Options& opt, const DArray<int>& predPrec, bool qkboPrecedence)
: PrecedenceOrdering(
    funcPrecFromOpts(prb,opt),
    predPrec,
    predLevelsFromOptsAndPrec(prb,opt,predPrec),
    opt.literalComparisonMode()==Shell::Options::LiteralComparisonMode::REVERSE,
    qkboPrecedence
    )
{
  CALL("PrecedenceOrdering::PrecedenceOrdering((Problem&,const Options&,const DArray<int>&)");
}

/**
 * Create a PrecedenceOrdering object.
 */
PrecedenceOrdering::PrecedenceOrdering(Problem& prb, const Options& opt, bool qkboPrecedence)
: PrecedenceOrdering(prb,opt,
    [&]() {
       // Make sure we (re-)compute usageCnt's for all the symbols;
       // in particular, the sP's (the Tseitin predicates) and sK's (the Skolem functions), which only exists since preprocessing.
       prb.getProperty();
       // also, fetch the unary minuses, and ones we intruduce later anyway
       (void)IntTraits::minusF();
       (void)RatTraits::minusF();
       (void)RealTraits::minusF();
       if (qkboPrecedence) {
         (void) IntTraits::oneF();
         (void) RatTraits::oneF();
         (void)RealTraits::oneF();
       }

       return predPrecFromOpts(prb, opt);
   }(),
   qkboPrecedence)
{
  CALL("PrecedenceOrdering::PrecedenceOrdering(Problem&,const Options&)");
  ASS_G(_predicates, 0);
}

static void sortAuxBySymbolPrecedence(DArray<unsigned>& aux, const Options& opt, bool forFunc) {
  CALL("sortAuxBySymbolPrecedence");

  switch(opt.symbolPrecedence()) {
    case Shell::Options::SymbolPrecedence::ARITY:
      aux.sort(BoostWrapper<ArityComparator<>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::REVERSE_ARITY:
      aux.sort(BoostWrapper<ArityComparator<true /*reverse*/>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::UNARY_FIRST:
      aux.sort(BoostWrapper<UnaryFirstComparator<false,ArityComparator<false,FreqComparator<>>>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::CONST_MAX:
      aux.sort(BoostWrapper<ConstFirstComparator<false,ArityComparator<>>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::CONST_MIN:
      aux.sort(BoostWrapper<ConstFirstComparator<true /*reverse*/,ArityComparator<true /*reverse*/>>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::FREQUENCY:
    case Shell::Options::SymbolPrecedence::WEIGHTED_FREQUENCY:
      aux.sort(BoostWrapper<FreqComparator<>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::REVERSE_FREQUENCY:
    case Shell::Options::SymbolPrecedence::REVERSE_WEIGHTED_FREQUENCY:
      aux.sort(BoostWrapper<FreqComparator<true /*reverse*/>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::UNARY_FREQ:
      aux.sort(BoostWrapper<UnaryFirstComparator<false,FreqComparator<>>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::CONST_FREQ:
      aux.sort(BoostWrapper<ConstFirstComparator<true /*reverse*/,FreqComparator<>>>(forFunc));
      break;
    case Shell::Options::SymbolPrecedence::OCCURRENCE:
      // already sorted by occurrence
      break;
    case Shell::Options::SymbolPrecedence::SCRAMBLE:
      unsigned sz = aux.size();
      for(unsigned i=0;i<sz;i++){
        unsigned j = Random::getInteger(sz-i)+i;
        unsigned tmp = aux[j];
        aux[j]=aux[i];
        aux[i]=tmp;
      }
      break;
  }
}

DArray<int> PrecedenceOrdering::funcPrecFromOpts(Problem& prb, const Options& opt) {
  unsigned nFunctions = env.signature->functions();
  DArray<unsigned> aux(nFunctions);

  if(nFunctions) {
    aux.initFromIterator(getRangeIterator(0u, nFunctions), nFunctions);

    if (!opt.functionPrecedence().empty()) {
      BYPASSING_ALLOCATOR;

      vstring precedence;
      ifstream precedence_file (opt.functionPrecedence().c_str());
      if (precedence_file.is_open() && getline(precedence_file, precedence)) {
        loadPermutationFromString(aux,precedence);
        precedence_file.close();
      }
    } else {
      sortAuxBySymbolPrecedence(aux,opt,true /* forFunc */);
    }
    
    /*cout << "Function precedences:" << endl;
    for(unsigned i=0;i<nFunctions;i++){
      cout << env.signature->functionName(aux[i]) << " ";
    }
    cout << endl;*/
    

    /*
    cout << "Function precedence: ";
    for(unsigned i=0;i<nFunctions;i++){
      cout << aux[i] << ",";
    }
    cout << endl;
    */

  }

  DArray<int>  functionPrecedences(nFunctions);
  for(unsigned i=0;i<nFunctions;i++) {
    functionPrecedences[aux[i]]=i;
  }
  return functionPrecedences;
}

DArray<int> PrecedenceOrdering::predPrecFromOpts(Problem& prb, const Options& opt) {
  unsigned nPredicates = env.signature->predicates();
  DArray<unsigned> aux(nPredicates);
  aux.initFromIterator(getRangeIterator(0u, nPredicates), nPredicates);

  if (!opt.predicatePrecedence().empty()) {
    BYPASSING_ALLOCATOR;

    vstring precedence;
    ifstream precedence_file (opt.predicatePrecedence().c_str());
    if (precedence_file.is_open() && getline(precedence_file, precedence)) {
      loadPermutationFromString(aux,precedence);
      precedence_file.close();
    }
  } else {
    sortAuxBySymbolPrecedence(aux,opt,false /* forFunc */);
  }
  /*
  cout << "Predicate precedences:" << endl;
  for(unsigned i=0;i<nPredicates;i++){
    cout << env.signature->predicateName(aux[i]) << " "; 
  }
  cout << endl;
  */
  /*
  cout << "Predicate precedence: ";
  for(unsigned i=0;i<nPredicates;i++){
    cout << aux[i] << ",";
  }
  cout << endl;
  */

  DArray<int> predicatePrecedences(nPredicates);
  for(unsigned i=0;i<nPredicates;i++) {
    predicatePrecedences[aux[i]]=i;
  }
  return predicatePrecedences;
}

namespace PredLevels {
  constexpr static int MIN_USER_DEF = 1; // equality has level 0, inequalities have level 1
  constexpr static int EQ = 0;
  constexpr static int INEQ = 0;
};


DArray<int> PrecedenceOrdering::predLevelsFromOptsAndPrec(Problem& prb, const Options& opt, const DArray<int>& predicatePrecedences) {
  unsigned nPredicates = env.signature->predicates();

  DArray<int> predicateLevels(nPredicates);

  switch(opt.literalComparisonMode()) {
  case Shell::Options::LiteralComparisonMode::STANDARD:
    predicateLevels.init(nPredicates, PredLevels::MIN_USER_DEF);
    break;
  case Shell::Options::LiteralComparisonMode::PREDICATE:
  case Shell::Options::LiteralComparisonMode::REVERSE:
    for(unsigned i=1;i<nPredicates;i++) {
      predicateLevels[i] = predicatePrecedences[i] + PredLevels::MIN_USER_DEF;
    }
    break;
  }
  //equality is on the lowest level
  predicateLevels[0] = PredLevels::EQ;

  if (env.predicateSineLevels) {
    // predicateSineLevels start from zero
    unsigned bound = env.maxSineLevel; // this is at least as large as the maximal value of a predicateSineLevel
    bool reverse = (opt.sineToPredLevels() == Options::PredicateSineLevels::ON); // the ON, i.e. reasonable, version wants low sine levels mapping to high predicateLevels

    for(unsigned i=1;i<nPredicates;i++) { // starting from 1, keeping predicateLevels[0]=0;
      unsigned level;
      if (!env.predicateSineLevels->find(i,level)) {
        level = bound;
      }
      predicateLevels[i] = (reverse ? (bound - level) : level) + PredLevels::MIN_USER_DEF;
      // cout << "setting predicate level of " << env.signature->predicateName(i) << " to " << predicateLevels[i] << endl;
    }
  }

  for(unsigned i=1;i<nPredicates;i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    //consequence-finding name predicates have the lowest level
    if(predSym->label()) {
      predicateLevels[i]=-1;
    }
    else if(predSym->equalityProxy()) {
      //equality proxy predicates have the highest level (lower than colored predicates)
      predicateLevels[i] = nPredicates + PredLevels::MIN_USER_DEF+ 1;
    }
    else if (predSym->interpreted()) {
      if (theory->isInequality(theory->interpretPredicate(i)) && env.options->termOrdering() == Options::TermOrdering::LALPO) {
        predicateLevels[i] = PredLevels::INEQ;
      }
    }
  }

  checkLevelAssumptions(predicateLevels);
  return predicateLevels;
}

void PrecedenceOrdering::checkLevelAssumptions(DArray<int> const& levels)
{
#if VDEBUG
  for (unsigned i = 0; i < levels.size(); i++) {
    if (theory->isInterpretedPredicate(i)) {
      auto itp = theory->interpretPredicate(i);
      if (itp == Kernel::Theory::EQUAL) {
        ASS(levels[i] == PredLevels::EQ);
      } else if (theory->isInequality(itp)) {
        ASS(env.options->termOrdering() != Options::TermOrdering::LALPO || levels[i] == PredLevels::INEQ);
      } else {
        ASS(levels[i] >= PredLevels::MIN_USER_DEF || levels[i] < 0)
      }
    }
  }
#endif // VDEBUG
}

void PrecedenceOrdering::show(ostream& out) const 
{
  CALL("PrecedenceOrdering::show(ostream& out)")
  {
    out << "% Function precedences, smallest symbols first (line format: `<name> <arity>`) " << std::endl;
    out << "% ===== begin of function precedences ===== " << std::endl;
    DArray<unsigned> functors;

    functors.initFromIterator(getRangeIterator(0u,env.signature->functions()),env.signature->functions());
    functors.sort(closureComparator([&](unsigned l, unsigned r){ return intoComparison(compareFunctionPrecedences(l,r)); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getFunction(functors[i]);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of function precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  {
    out << "% Predicate precedences, smallest symbols first (line format `<name> <arity>`) " << std::endl;
    out << "% ===== begin of predicate precedences ===== " << std::endl;

    DArray<unsigned> functors;
    functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
    functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(_predicatePrecedences[l], _predicatePrecedences[r]); }));
    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getPredicate(functors[i]);
      out << "% " << sym->name() << " " << sym->arity() << std::endl;
    }

    out << "% ===== end of predicate precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  {
    out << "% Predicate levels (line format: `<name> <arity> <level>`)" << std::endl;
    out << "% ===== begin of predicate levels ===== " << std::endl;

    DArray<unsigned> functors;
    functors.initFromIterator(getRangeIterator(0u,env.signature->predicates()),env.signature->predicates());
    functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(_predicateLevels[l], _predicateLevels[r]); }));

    for (unsigned i = 0; i < functors.size(); i++) {
      auto sym = env.signature->getPredicate(i);
      out << "% " << sym->name() << " " << sym->arity() << " " << _predicateLevels[i] << std::endl;
    }

    out << "% ===== end of predicate precedences ===== " << std::endl;
  }

  out << "%" << std::endl;

  showConcrete(out);
}

DArray<int> PrecedenceOrdering::testLevels() 
{
  DArray<int> levels(env.signature->predicates());
  for (unsigned i = 0; i < levels.size(); i++) {
    if (theory->isInterpretedPredicate(i)) {
      auto itp = theory->interpretPredicate(i);
      if (itp == Kernel::Theory::EQUAL) {
        levels[i] = PredLevels::EQ;
      } else if (theory->isInequality(itp)) {
        levels[i] = PredLevels::INEQ;
      } else {
        levels[i] = PredLevels::MIN_USER_DEF;
      }
    }
  }
  return levels;
}
