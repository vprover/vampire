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
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Set.hpp"
#include "Shell/Shuffling.hpp"

#include "Shell/Options.hpp"
#include <fstream>

#include "KBOComparator.hpp"
#include "NumTraits.hpp"
#include "Signature.hpp"
#include "SubstHelper.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"

#include "KBO.hpp"

#define COLORED_WEIGHT_BOOST 0x10000

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result KBO::State::result(KBO const& kbo, AppliedTerm t1, AppliedTerm t2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1.term.term()->functor()!=t2.term.term()->functor()) {
    if(t1.term.term()->isLiteral()) {
      int prec1, prec2;
      prec1=kbo.predicatePrecedence(t1.term.term()->functor());
      prec2=kbo.predicatePrecedence(t2.term.term()->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else if(t1.term.term()->isSort()){
      ASS(t2.term.term()->isSort()); //should only compare sorts with sorts
      res=kbo.compareTypeConPrecedences(t1.term.term()->functor(), t2.term.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    } else {
      res=kbo.compareFunctionPrecedences(t1.term.term()->functor(), t2.term.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  return res;
}

Ordering::Result KBO::State::innerResult(KBO const& kbo, TermList tl1, TermList tl2)
{
  ASS(!TermList::sameTopFunctor(tl1,tl2));

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(tl1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(tl2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else if(tl1.term()->isSort()){
      res=kbo.compareTypeConPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    } else {
      res=kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

template<int coef>
void KBO::State::recordVariable(unsigned var)
{
  static_assert(coef==1 || coef==-1);

  auto& ref = _varDiffs[var];
  ref += coef;
  if constexpr (coef==1) {
    if(ref==0) {
      _negNum--;
    } else if(ref==1) {
      _posNum++;
    }
  } else {
    if(ref==0) {
      _posNum--;
    } else if(ref==-1) {
      _negNum++;
    }
  }
}

template<int coef>
void KBO::State::traverse(KBO const& kbo, AppliedTerm tt)
{
  static_assert(coef==1 || coef==-1);

  if (tt.term.isVar()) {
    _weightDiff += kbo._funcWeights._specialWeights._variableWeight * coef;
    recordVariable<coef>(tt.term.var());
    return;
  }
  struct State {
    AppliedTerm t;
    unsigned arg;
  };
  static Stack<State> recState;
  recState.push(State{ tt, 0 });

  _weightDiff += kbo.symbolWeight(tt.term.term()) * coef;

  while (recState.isNonEmpty()) {
    auto& curr = recState.top();
    if (curr.arg >= curr.t.term.term()->arity()) {
      recState.pop();
      continue;
    }
    AppliedTerm t(*curr.t.term.term()->nthArgument(curr.arg++), curr.t);
    if (t.term.isVar()) {
      ASS(!t.aboveVar);
      _weightDiff += kbo._funcWeights._specialWeights._variableWeight * coef;
      recordVariable<coef>(t.term.var());
      continue;
    }

    _weightDiff += kbo.symbolWeight(t.term.term()) * coef;
    recState.push(State{ t, 0 });
  }
}

template void KBO::State::traverse<1>(KBO const&, AppliedTerm);
template void KBO::State::traverse<-1>(KBO const&, AppliedTerm);

Ordering::Result KBO::State::traverseLexBidir(KBO const& kbo, AppliedTerm tl1, AppliedTerm tl2)
{
  ASS(tl1.term.isTerm() && tl2.term.isTerm());
  auto t1 = tl1.term.term();
  auto t2 = tl2.term.term();

  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<pair<const TermList*,bool>> stack(32);
  stack.reset();
  stack.push(make_pair(t1->args(),tl1.aboveVar));
  stack.push(make_pair(t2->args(),tl2.aboveVar));
  while(!stack.isEmpty()) {
    auto [tt,ttAboveVar] = stack.pop(); // tl2 subterm
    auto [ss,ssAboveVar] = stack.pop(); // tl1 subterm
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
        lexValidDepth=depth;
        if(_weightDiff!=0) {
          _lexResult=_weightDiff>0 ? GREATER : LESS;
        }
        _lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(make_pair(ss->next(),ssAboveVar));
    stack.push(make_pair(tt->next(),ttAboveVar));

    AppliedTerm s(*ss,tl1.applicator,ssAboveVar);
    AppliedTerm t(*tt,tl2.applicator,ttAboveVar);

    if(s.equalsShallow(t)) {
      //if content is the same, neither weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(s.term,t.term)) {
      ASS(s.term.isTerm());
      ASS(t.term.isTerm());
      ASS(s.term.term()->arity());
      stack.push(make_pair(s.term.term()->args(),s.aboveVar));
      stack.push(make_pair(t.term.term()->args(),t.aboveVar));
      depth++;
    } else {
      traverse<1>(kbo, s);
      traverse<-1>(kbo, t);
      if(_lexResult==EQUAL) {
        _lexResult=innerResult(kbo, s.term, t.term);
        lexValidDepth=depth;
        ASS(_lexResult!=EQUAL);
      }
    }
  }
  return result(kbo, tl1, tl2);
}

Ordering::Result KBO::State::traverseLexUnidir(KBO const& kbo, AppliedTerm tl1, AppliedTerm tl2)
{
  ASS(tl1.term.isTerm() && tl2.term.isTerm());
  auto t1 = tl1.term.term();
  auto t2 = tl2.term.term();

  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());

  static Stack<pair<const TermList*,bool>> stack(32);
  stack.reset();
  stack.push(make_pair(t1->args(),tl1.aboveVar));
  stack.push(make_pair(t2->args(),tl2.aboveVar));
  while(!stack.isEmpty()) {
    auto [tt,ttAboveVar] = stack.pop(); // tl2 subterm
    auto [ss,ssAboveVar] = stack.pop(); // tl1 subterm
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      continue;
    }

    stack.push(make_pair(ss->next(),ssAboveVar));
    stack.push(make_pair(tt->next(),ttAboveVar));

    AppliedTerm s(*ss,tl1.applicator,ssAboveVar);
    AppliedTerm t(*tt,tl2.applicator,ttAboveVar);

    if(s.equalsShallow(t)) {
      //if content is the same, neither weightDiff nor varDiffs would change
      continue;
    }
    // ssw == ttw
    if (s.term.isVar()) {
      return INCOMPARABLE;
    }
    if (t.term.isVar()) {
      return s.containsVar(t.term) ? GREATER : INCOMPARABLE;
    }
    auto wcomp = kbo.positivityCheck(s,t);
    if (wcomp != EQUAL) {
      return wcomp;
    }
    ASS(s.term.isTerm());
    ASS(t.term.isTerm());
    Result comp = s.term.term()->isSort()
      ? kbo.compareTypeConPrecedences(s.term.term()->functor(),t.term.term()->functor())
      : kbo.compareFunctionPrecedences(s.term.term()->functor(),t.term.term()->functor());
    switch (comp)
    {
      case Ordering::LESS:
        return INCOMPARABLE;
      case Ordering::GREATER:
        return GREATER;
      case Ordering::EQUAL:
        stack.push(make_pair(s.term.term()->args(),s.aboveVar));
        stack.push(make_pair(t.term.term()->args(),t.aboveVar));
        break;
      default: ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
struct PredSigTraits {
  static const char* symbolKindName() 
  { return "predicate"; }

  static unsigned nSymbols() 
  { return env.signature->predicates(); }

  static bool isColored(unsigned functor) 
  { return env.signature->predicateColored(functor);}

  static bool tryGetFunctor(const std::string& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetPredicateNumber(sym,arity, out); }

  static const std::string& weightFileName(const Options& opts) 
  { return opts.predicateWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return false; }

  static bool isConstantSymbol(unsigned functor) 
  { return false; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getPredicate(functor); } 
};
#endif


struct FuncSigTraits {
  static const char* symbolKindName() 
  { return "function"; }

  static unsigned nSymbols() 
  { return env.signature->functions(); } 

  static bool isColored(unsigned functor) 
  { return env.signature->functionColored(functor);}

  static bool tryGetFunctor(const std::string& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetFunctionNumber(sym,arity, out); }

  static const std::string& weightFileName(const Options& opts) 
  { return opts.functionWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return env.signature->getFunction(functor)->numTermArguments() == 1; } 

  static bool isConstantSymbol(unsigned functor) 
  { return env.signature->getFunction(functor)->numTermArguments() == 0; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getFunction(functor); }
};


template<class SigTraits> 
KboWeightMap<SigTraits> KBO::weightsFromOpts(const Options& opts, const DArray<int>& rawPrecedence) const
{
  auto& str = SigTraits::weightFileName(opts);

  auto arityExtractor = [](unsigned i) { return SigTraits::getSymbol(i)->arity(); };
  auto precedenceExtractor = [&](unsigned i) { return rawPrecedence[i]; };
  auto frequencyExtractor = [](unsigned i) { return SigTraits::getSymbol(i)->usageCnt(); };

  if (!str.empty()) {
    return weightsFromFile<SigTraits>(opts);
  } else {
    switch (opts.kboWeightGenerationScheme()) {
    case Options::KboWeightGenerationScheme::CONST:
      return KboWeightMap<SigTraits>::dflt();
    case Options::KboWeightGenerationScheme::RANDOM:
      return KboWeightMap<SigTraits>::randomized();
    case Options::KboWeightGenerationScheme::ARITY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto _, auto arity) { return arity+1; });
    case Options::KboWeightGenerationScheme::INV_ARITY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto max, auto arity) { return max-arity+1; });
    case Options::KboWeightGenerationScheme::ARITY_SQUARED:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto _, auto arity) { return arity*arity+1; });
    case Options::KboWeightGenerationScheme::INV_ARITY_SQUARED:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto max, auto arity) { return max*max-arity*arity+1; });
    case Options::KboWeightGenerationScheme::PRECEDENCE:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(precedenceExtractor,
        [](auto _, auto prec) { return prec + 1; });
    case Options::KboWeightGenerationScheme::INV_PRECEDENCE:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(precedenceExtractor,
        [](auto max, auto prec) { return max-prec+1; });
    case Options::KboWeightGenerationScheme::FREQUENCY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(frequencyExtractor,
        [](auto _, auto freq) { return freq > 0 ? freq : 1; });
    case Options::KboWeightGenerationScheme::INV_FREQUENCY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(frequencyExtractor,
        [](auto max, auto freq) { return max > 0 ? max - freq + 1 : 1; });

    default:
      NOT_IMPLEMENTED;
    }
  }
}

template<class SigTraits> 
KboWeightMap<SigTraits> KBO::weightsFromFile(const Options& opts) const 
{
  DArray<KboWeight> weights(SigTraits::nSymbols());

  ///////////////////////// parsing helper functions ///////////////////////// 
 
  /** opens the file with name f or throws a UserError on failure  */
  auto openFile = [](const std::string& f) -> ifstream {
    ifstream file(f.c_str());
    if (!file.is_open()) {
      throw UserErrorException("failed to open file ", f);
    }
    return file;
  };

  auto parseDefaultSymbolWeight = [&openFile](const std::string& fname) -> unsigned {
    if (!fname.empty()) {
      auto file = openFile(fname);
      for (std::string ln; getline(file, ln);) {
        unsigned dflt;
        std::string special_name;
        bool err = !(std::stringstream(ln) >> special_name >> dflt);
        if (!err && special_name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) {
          return dflt;
        }
      }
    }
    return 1; // the default defaultSymbolWeight ;) 
  };

  /** tries to parse line of the form `<special_name> <weight>` */
  auto tryParseSpecialLine = [](const std::string& ln, unsigned& introducedWeight, KboSpecialWeights<SigTraits>& specialWeights) -> bool {
    std::stringstream lnstr(ln);

    std::string name;
    unsigned weight;
    bool ok = !!(lnstr >> name >> weight);
    if (ok) {
      if (specialWeights.tryAssign(name, weight)) { return true; }
      else if (name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) { /* handled in parseDefaultSymbolWeight */ }
      else if (name == SPECIAL_WEIGHT_IDENT_INTRODUCED    ) { introducedWeight = weight; } 
      else {
        throw Lib::UserErrorException("no special symbol with name '", name, "' (existing ones: " SPECIAL_WEIGHT_IDENT_VAR ", " SPECIAL_WEIGHT_IDENT_INTRODUCED " )");
      }
    }
    return ok;
  };

  /** tries to parse line of the form `<name> <arity> <weight>` */
  auto tryParseNormalLine = [&](const std::string& ln) -> bool {
    std::stringstream lnstr(ln);

    std::string name;
    unsigned arity;
    unsigned weight;
    bool ok = !!(lnstr >> name >> arity >> weight);
    if (ok) {
      unsigned i; 
      if (SigTraits::tryGetFunctor(name, arity, i)) {
        weights[i] = SigTraits::isColored(i) 
          ? weight * COLORED_WEIGHT_BOOST
          : weight;
      } else {
        throw Lib::UserErrorException("no ", SigTraits::symbolKindName(), " '", name, "' with arity ", arity);
      }
    }
    return ok;
  };

  ///////////////////////// actual parsing ///////////////////////// 

  auto& filename = SigTraits::weightFileName(opts);
  auto defaultSymbolWeight = parseDefaultSymbolWeight(filename);

  for (unsigned i = 0; i < SigTraits::nSymbols(); i++) {
    weights[i] = SigTraits::isColored(i) 
          ? defaultSymbolWeight * COLORED_WEIGHT_BOOST 
          : defaultSymbolWeight;
  }

  unsigned introducedWeight = defaultSymbolWeight;
  auto specialWeights = KboSpecialWeights<SigTraits>::dflt();

  ASS(!filename.empty());

  auto file = openFile(filename);

  for (std::string ln; getline(file, ln);) {
    if (!tryParseNormalLine(ln) && !tryParseSpecialLine(ln, introducedWeight, specialWeights)) {
      throw Lib::UserErrorException(
             "failed to read line from file ",   filename, "\n",
             "expected syntax: '<name> <arity> <weight>'", "\n",
             "e.g.:            '$add   2       4       '", "\n",
             "or syntax: '<special_name> <weight>'"      , "\n",
             "e.g.:      '$var           7       '"      , "\n"
      );
    } 
  }

  return KboWeightMap<SigTraits> {
    ._weights                = weights.clone(),
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = specialWeights,
  };

}

void throwError(UserErrorException e) { throw e; }
void warnError(UserErrorException e) {
  std::cout << "WARNING: Your KBO is probably not well-founded. Reason: " << e.msg() << std::endl;
}


KBO::KBO(
    // KBO params
    KboWeightMap<FuncSigTraits> funcWeights, 
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
    KboWeightMap<PredSigTraits> predWeights, 
#endif

    // precedence ordering params
    DArray<int> funcPrec,
    DArray<int> typeConPrec,     
    DArray<int> predPrec, 
    DArray<int> predLevels, 

    // other
    bool reverseLCM
  ) : PrecedenceOrdering(funcPrec, typeConPrec, predPrec, predLevels, reverseLCM)
  , _funcWeights(funcWeights)
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  , _predWeights(predWeights)
#endif
{ 
  checkAdmissibility(throwError);
}

KBO KBO::testKBO(bool rand)
{
  auto predLevels = []() -> DArray<int>
    { return PrecedenceOrdering::testLevels(); };

  auto prec = [&](int size) {
    auto out = DArray<int>::fromIterator(range(0,size));
    if (rand) {
      Shuffling::shuffleArray(out, size);
    }
    return out;
  };
  return KBO(
      rand ? KboWeightMap<FuncSigTraits>::randomized() : KboWeightMap<FuncSigTraits>::dflt(),
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
      rand ? KboWeightMap<PredSigTraits>::randomized() : KboWeightMap<PredSigTraits>::dflt(),
#endif
      prec(env.signature->functions()),
      prec(env.signature->typeCons()),
      prec(env.signature->predicates()),
      predLevels(),
      /*reverseLCM=*/false);
}

void KBO::zeroWeightForMaximalFunc() {
  // actually, it's non-constant maximal func, as constants cannot be weight 0

  using FunctionSymbol = unsigned;
  auto nFunctions = _funcWeights._weights.size();
  if (!nFunctions) {
    return;
  }

  FunctionSymbol maxFn = 0;
  for (FunctionSymbol i = 1; i < nFunctions; i++) {
    if (compareFunctionPrecedences(maxFn, i) == LESS) {
      maxFn = i;
    }
  }

  auto symb = env.signature->getFunction(maxFn);
  auto arity = symb->numTermArguments();

  // skip constants here (they mustn't be lighter than $var)
  if (arity != 0){
    _funcWeights._weights[maxFn] = 0;
  }
}

template<class HandleError>
void KBO::checkAdmissibility(HandleError handle) const 
{
  using FunctionSymbol = unsigned;
  auto nFunctions = _funcWeights._weights.size();

  FunctionSymbol maxFn = 0; // only properly initialized when (nFunctions > 0)
  for (FunctionSymbol i = 1; i < nFunctions; i++) {
    if (compareFunctionPrecedences(maxFn, i) == LESS) {
      maxFn = i;
    }
  }

  // TODO remove unary minus check once new 
  // theory calculus goes into master
  auto isUnaryMinus = [](unsigned functor){
    return theory->isInterpretedFunction(functor, IntTraits::minusI) ||
           theory->isInterpretedFunction(functor, RatTraits::minusI) ||
           theory->isInterpretedFunction(functor, RealTraits::minusI);
  };

  ////////////////// check kbo-releated constraints //////////////////
  unsigned varWght = _funcWeights._specialWeights._variableWeight;

  for (unsigned i = 0; i < nFunctions; i++) {
    auto arity = env.signature->getFunction(i)->numTermArguments();

    if (_funcWeights._weights[i] < varWght && arity == 0) {
      handle(UserErrorException("weight of constants (i.e. ", env.signature->getFunction(i)->name(), ") must be greater or equal to the variable weight (", varWght, ")"));

    } else if (_funcWeights.symbolWeight(i) == 0 && arity == 1 && maxFn != i && !isUnaryMinus(i)) {
      handle(UserErrorException( "a unary function of weight zero (i.e.: ", env.signature->getFunction(i)->name(), ") must be maximal wrt. the precedence ordering"));

    }
  }

  if (_funcWeights._introducedSymbolWeight < varWght) {
    handle(UserErrorException("weight of introduced function symbols must be greater than the variable weight (= ", varWght, "), since there might be new constant symbols introduced during proof search."));
  }


  if ( _funcWeights._specialWeights._numReal < varWght
    || _funcWeights._specialWeights._numInt  < varWght
    || _funcWeights._specialWeights._numRat  < varWght
      ) {
    handle(UserErrorException("weight of (number) constant symbols must be >= variable weight (", varWght, ")."));
  }

  if (varWght <= 0) {
    handle(UserErrorException("variable weight must be greater than zero"));
  }
}


/**
 * Create a KBO object.
 */
KBO::KBO(Problem& prb, const Options& opts)
 : PrecedenceOrdering(prb, opts)
 , _funcWeights(weightsFromOpts<FuncSigTraits>(opts,_functionPrecedences))
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
 , _predWeights(weightsFromOpts<PredSigTraits>(opts,_predicatePrecedences))
#endif
{
  if (opts.kboMaxZero()) {
    zeroWeightForMaximalFunc();
  }

  if (opts.kboAdmissabilityCheck() == Options::KboAdmissibilityCheck::ERROR)
    checkAdmissibility(throwError);
  else
    checkAdmissibility(warnError);
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::comparePredicates(Literal* l1, Literal* l2) const
{
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  static State state;
  state.reset();

  if(p1==p2) {
    return state.traverseLexBidir(*this, AppliedTerm(TermList(l1)),AppliedTerm(TermList(l2)));
  }

  TermList* ts;
  ts=l1->args();
  while(!ts->isEmpty()) {
    state.traverse<1>(*this, AppliedTerm(*ts));
    ts=ts->next();
  }
  ts=l2->args();
  while(!ts->isEmpty()) {
    state.traverse<-1>(*this, AppliedTerm(*ts));
    ts=ts->next();
  }
  return state.result(*this, AppliedTerm(TermList(l1)),AppliedTerm(TermList(l2)));
} // KBO::comparePredicates()

Ordering::Result KBO::compare(TermList tl1, TermList tl2) const
{
  return compare(AppliedTerm(tl1),AppliedTerm(tl2));
}

Ordering::Result KBO::compare(AppliedTerm tl1, AppliedTerm tl2) const
{
  if(tl1.equalsShallow(tl2)) {
    return EQUAL;
  }
  if(tl1.term.isVar()) {
    return tl2.containsVar(tl1.term) ? LESS : INCOMPARABLE;
  }
  if(tl2.term.isVar()) {
    return tl1.containsVar(tl2.term) ? GREATER : INCOMPARABLE;
  }

  ASS(tl1.term.isTerm());
  ASS(tl2.term.isTerm());

  Term* t1=tl1.term.term();
  Term* t2=tl2.term.term();

  static State state;
  state.reset();

  if(t1->functor()==t2->functor()) {
    return state.traverseLexBidir(*this, tl1, tl2);
  }

  state.traverse<1>(*this, tl1);
  state.traverse<-1>(*this, tl2);
  return state.result(*this, tl1, tl2);
}

Ordering::Result KBO::compareUnidirectional(AppliedTerm tl1, AppliedTerm tl2) const
{
  if (this != tryGetGlobalOrdering()) {
    return compare(tl1, tl2);
  }
  if (tl1.equalsShallow(tl2)) {
    return EQUAL;
  }
  if (tl1.term.isVar()) {
    return INCOMPARABLE;
  }
  if (tl2.term.isVar()) {
    return tl1.containsVar(tl2.term) ? GREATER : INCOMPARABLE;
  }

  ASS(tl1.term.isTerm());
  ASS(tl2.term.isTerm());

  Term* t1=tl1.term.term();
  Term* t2=tl2.term.term();

  auto wcomp = positivityCheck(tl1,tl2);
  if (wcomp != EQUAL) {
    return wcomp;
  }

  // w1==w2
  Result comp = t1->isSort()
    ? compareTypeConPrecedences(t1->functor(),t2->functor())
    : compareFunctionPrecedences(t1->functor(),t2->functor());
  switch (comp)
  {
    case Ordering::LESS:
      return INCOMPARABLE;
    case Ordering::GREATER:
      return GREATER;
    case Ordering::EQUAL: {
      static State state;
      state.reset();
      return state.traverseLexUnidir(*this, tl1, tl2);
    }
    default:
      ASSERTION_VIOLATION;
  }
}

OrderingComparatorUP KBO::createComparator() const
{
  return make_unique<KBOComparator>(*this);
}

int KBO::symbolWeight(const Term* t) const
{
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  if (t->isLiteral()) 
    return _predWeights.symbolWeight(t);
  else 
#endif
  if (t->isSort()){
    //For now just give all type constructors minimal weight
    return _funcWeights._specialWeights._variableWeight;
  }
  return _funcWeights.symbolWeight(t);
}

const LinearExpression* KBO::computeWeight(Term* t) const
{
  ASS(tryGetGlobalOrdering() == this);

  auto linexp = static_cast<const LinearExpression*>(t->kboLinExp(this));
  if (linexp) {
    return linexp;
  }
  // stack of [non-zero arity terms, current argument position, accumulated weight]
  struct State {
    State(Term* t) : t(t) {}
    Term* t;
    unsigned arg = 0;
    unsigned constant = 0;
    ZIArray<int> varCoeffs;
  };
  static Stack<State> recState;
  recState.push(t);

  while (recState.isNonEmpty()) {
    auto& curr = recState.top();
    if (curr.arg < curr.t->arity()) {
      auto arg = *curr.t->nthArgument(curr.arg++);

      if (arg.isVar()) {
        curr.varCoeffs[arg.var()]++;
        continue;
      }

      // if we already cached linear expression
      // for arg, use it, otherwise compute it
      auto arg_linexp = static_cast<const LinearExpression*>(arg.term()->kboLinExp(this));
      if (arg_linexp) {
        curr.constant += arg_linexp->constant;
        for (const auto& [var, coeff] : arg_linexp->varCoeffPairs) {
          curr.varCoeffs[var] += coeff;
        }
      } else {
        recState.push(arg.term());
      }

    } else {

      auto orig = recState.pop();
      orig.constant += symbolWeight(orig.t);
      Stack<VarCoeffPair> res;
      for (unsigned i = 0; i < orig.varCoeffs.size(); i++) {
        if (orig.varCoeffs[i]) {
          res.push({ i, orig.varCoeffs[i] });
        }
      }
      auto linexp = LinearExpression::get(orig.constant, res);
      orig.t->setKboLinExp(linexp, this);

      if (recState.isEmpty()) {
        return linexp;
      }

      recState.top().constant += orig.constant;
      for (unsigned i = 0; i < orig.varCoeffs.size(); i++) {
        recState.top().varCoeffs[i] += orig.varCoeffs[i];
      }
    }
  }
  ASSERTION_VIOLATION;
}

Result KBO::positivityCheck(AppliedTerm t1, AppliedTerm t2) const
{
  ASS(tryGetGlobalOrdering() == this);
  ASS(t1.term.isTerm());
  ASS(t2.term.isTerm());

  int weight = 0;
  static ZIArray<int> varDiffs;
  varDiffs.reset();

  ALWAYS(positivityCheck2</*sign=*/1>(weight, varDiffs, computeWeight(t1.term.term()), t1));
  if (!positivityCheck2</*sign=*/-1>(weight, varDiffs, computeWeight(t2.term.term()), t2)) {
    return INCOMPARABLE;
  }

  if (weight > 0) {
    return GREATER;
  } else if (weight == 0) {
    return EQUAL;
  }
  return INCOMPARABLE;
}

template<int sign>
bool KBO::positivityCheck2(int& weight, ZIArray<int>& varDiffs, const LinearExpression* linexp, AppliedTerm parent) const
{
  static_assert(sign==1 || sign==-1);

  weight += sign * linexp->constant;
  for (const auto& [var, coeff] : linexp->varCoeffPairs) {
    AppliedTerm tt(TermList::var(var), parent);
    if (tt.term.isVar()) {
      varDiffs[tt.term.var()] += sign * coeff;
      weight += sign * coeff * _funcWeights._specialWeights._variableWeight;
      if (varDiffs[tt.term.var()]<0) {
        return false;
      }
    } else {
      auto varLinExp = computeWeight(tt.term.term());
      weight += sign * coeff * varLinExp->constant;
      for (const auto& [varInner, coeffInner] : varLinExp->varCoeffPairs) {
        weight += sign * coeff * coeffInner * _funcWeights._specialWeights._variableWeight;
        varDiffs[varInner] += sign * coeff * coeffInner;
        if (varDiffs[varInner]<0) {
          return false;
        }
      }
    }
  }
  return true;
}

template<class SigTraits>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::dflt()
{
  return KboWeightMap {
    ._weights                = DArray<KboWeight>::initialized(SigTraits::nSymbols(), 1),
    ._introducedSymbolWeight = 1,
    ._specialWeights         = KboSpecialWeights<SigTraits>::dflt(),
  };
}

template<class SigTraits>
template<class Extractor, class Fml>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::fromSomeUnsigned(Extractor ex, Fml fml)
{
  auto nSym = SigTraits::nSymbols();
  DArray<KboWeight> weights(nSym);

  decltype(ex(0)) max = 0;
  for (unsigned i = 0; i < nSym; i++) {
    auto a = ex(i);
    if (a > max) {
      max = a;
    }
  }

  for (unsigned i = 0; i < nSym; i++) {
    weights[i] = fml(max,ex(i));
  }

  return KboWeightMap {
    ._weights                = weights.clone(),
    ._introducedSymbolWeight = 1,
    ._specialWeights         = KboSpecialWeights<SigTraits>::dflt(),
  };
}


template<>
template<class Random>
KboWeightMap<FuncSigTraits> KboWeightMap<FuncSigTraits>::randomized(unsigned maxWeight, Random random)
{
  using SigTraits = FuncSigTraits;
  auto nSym = SigTraits::nSymbols();

  unsigned variableWeight   = 1;
  unsigned introducedWeight = random(variableWeight, maxWeight);
  unsigned numInt           = random(variableWeight, maxWeight);
  unsigned numRat           = random(variableWeight, maxWeight);
  unsigned numReal          = random(variableWeight, maxWeight);

  DArray<KboWeight> weights(nSym);
  for (unsigned i = 0; i < nSym; i++) {
    if (SigTraits::isConstantSymbol(i)) {
      weights[i] = random(variableWeight, maxWeight);
    } else if (SigTraits::isUnaryFunction(i)) {
      // TODO support one zero-weight-unary-function per sort
      weights[i] = random(1, maxWeight); 
    } else {
      weights[i] = random(0, maxWeight);
    }
  }

  return KboWeightMap {
    ._weights                = weights.clone(),
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = KboSpecialWeights<FuncSigTraits> {
      ._variableWeight = variableWeight,
      ._numInt     =  numInt,
      ._numRat     =  numRat,
      ._numReal    =  numReal,
    },
  };
}

template<class SigTraits>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::randomized()
{ return randomized(1 << 16, [](unsigned min, unsigned max) { return min + Random::getInteger(max - min); }); }

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template<>
template<class Random>
KboWeightMap<PredSigTraits> KboWeightMap<PredSigTraits>::randomized(unsigned maxWeight, Random random)
{
  using SigTraits = FuncSigTraits;
  auto nSym = SigTraits::nSymbols();

  unsigned introducedWeight = random(0, maxWeight);

  DArray<KboWeight> weights(nSym);
  for (unsigned i = 0; i < nSym; i++) {
    weights[i] = random(0, maxWeight);
  }

  return KboWeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = KboSpecialWeights<PredSigTraits>{},
  };
}
#endif

template<class SigTraits>
KboWeight KboWeightMap<SigTraits>::symbolWeight(const Term* t) const
{
  return symbolWeight(t->functor());
}

template<class SigTraits>
KboWeight KboWeightMap<SigTraits>::symbolWeight(unsigned functor) const
{

  unsigned weight;
  if (!_specialWeights.tryGetWeight(functor, weight)) {
    weight = functor < _weights.size() ? _weights[functor]
                                       : _introducedSymbolWeight;
  }
  return weight;
}

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
void showSpecialWeights(const KboSpecialWeights<PredSigTraits>& ws, ostream& out) 
{ }
#endif

void showSpecialWeights(const KboSpecialWeights<FuncSigTraits>& ws, ostream& out) 
{ 
  out << "% " SPECIAL_WEIGHT_IDENT_VAR        " " << ws._variableWeight         << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_REAL   " " << ws._numReal                << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_RAT    " " << ws._numRat                 << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_INT    " " << ws._numInt                 << std::endl;
}
template<class SigTraits>
void KBO::showConcrete_(ostream& out) const  
{
  out << "% Weights of " << SigTraits::symbolKindName() << " (line format: `<name> <arity> <weight>`)" << std::endl;
  out << "% ===== begin of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;
  

  auto& map = getWeightMap<SigTraits>();
  DArray<unsigned> functors;
  functors.initFromIterator(getRangeIterator(0u,SigTraits::nSymbols()),SigTraits::nSymbols());
  functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(map.symbolWeight(l), map.symbolWeight(r)); }));

  for (unsigned i = 0; i < SigTraits::nSymbols(); i++) {
    auto functor = functors[i];
    auto sym = SigTraits::getSymbol(functor);
    out << "% " << sym->name() << " " << sym->arity() << " " << map.symbolWeight(functor) << std::endl;
  }

  auto& ws = getWeightMap<SigTraits>();
  out << "% " SPECIAL_WEIGHT_IDENT_INTRODUCED " " << ws._introducedSymbolWeight << std::endl;
  showSpecialWeights(ws._specialWeights, out);

  out << "% ===== end of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;

}
void KBO::showConcrete(ostream& out) const  
{
  showConcrete_<FuncSigTraits>(out);
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  out << "%" << std::endl;
  showConcrete_<PredSigTraits>(out);
#endif
}

template<> const KboWeightMap<FuncSigTraits>& KBO::getWeightMap<FuncSigTraits>() const 
{ return _funcWeights; }

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template<> const KboWeightMap<PredSigTraits>& KBO::getWeightMap<PredSigTraits>() const 
{ return _predWeights; }
#endif



#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
bool KboSpecialWeights<PredSigTraits>::tryGetWeight(unsigned functor, unsigned& weight) const
{ return false; }
#endif

bool KboSpecialWeights<FuncSigTraits>::tryGetWeight(unsigned functor, unsigned& weight) const
{
  if (env.signature->isFoolConstantSymbol(false,functor) || env.signature->isFoolConstantSymbol(true,functor)) {
    // the FOOL constants, $$false and $$true, introduced by us to deal with FOOL, have hard-coded weight of 1
    // which, together with their lowest precendence (see PrecedenceOrdering::compareFunctionPrecedences),
    // is a requirement for FOOL paramodulation being complete for them
    // TODO: consider allowing the user to change this and at the same time automatically recognizing the incomplete versions
    weight = 1;  return true;
  }
  auto sym = env.signature->getFunction(functor);
    if (sym->integerConstant())  { weight = _numInt;  return true; }
    if (sym->rationalConstant()) { weight = _numRat;  return true; }
    if (sym->realConstant())     { weight = _numReal; return true; }
    if (env.options->pushUnaryMinus()) {
      if (theory->isInterpretedFunction(functor, IntTraits ::minusI)) { weight = 0; return true; }
      if (theory->isInterpretedFunction(functor, RatTraits ::minusI)) { weight = 0; return true; }
      if (theory->isInterpretedFunction(functor, RealTraits::minusI)) { weight = 0; return true; }
    }
  return false;
}

template KboWeightMap<FuncSigTraits> KboWeightMap<FuncSigTraits>::dflt();
template KboWeight KboWeightMap<FuncSigTraits>::symbolWeight(const Term*) const;
template KboWeight KboWeightMap<FuncSigTraits>::symbolWeight(unsigned) const;
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template KboWeightMap<PredSigTraits> KboWeightMap<PredSigTraits>::dflt();
template KboWeight KboWeightMap<PredSigTraits>::symbolWeight(unsigned) const;
#endif

// LinearExpression

const LinearExpression* LinearExpression::get(int constant, const Stack<VarCoeffPair>& varCoeffPairs)
{
  static Set<LinearExpression*, DerefPtrHash<DefaultHash>> polys;

  sort(varCoeffPairs.begin(),varCoeffPairs.end(),[](const auto& vc1, const auto& vc2) {
    auto vc1pos = vc1.second>0;
    auto vc2pos = vc2.second>0;
    return (vc1pos && !vc2pos) || (vc1pos == vc2pos && vc1.first<vc2.first);
  });

  LinearExpression poly{ constant, varCoeffPairs };
  // The code below depends on the fact that the first argument
  // is only called when poly is not used anymore, otherwise the
  // move would give undefined behaviour.
  bool unused;
  return polys.rawFindOrInsert(
    [&](){ return new LinearExpression(std::move(poly)); },
    poly.defaultHash(),
    [&](LinearExpression* p) { return *p == poly; },
    unused);
}

std::ostream& operator<<(std::ostream& out, const LinearExpression& poly)
{
  bool first = true;
  for (const auto& [var, coeff] : poly.varCoeffPairs) {
    if (coeff > 0) {
      out << (first ? "" : " + ");
    } else {
      out << (first ? "- " : " - ");
    }
    first = false;
    auto abscoeff = std::abs(coeff);
    if (abscoeff!=1) {
      out << abscoeff << " * ";
    }
    out << TermList::var(var);
  }
  if (poly.constant) {
    out << (poly.constant<0 ? " - " : " + ");
    out << std::abs(poly.constant);
  }
  return out;
}

}
