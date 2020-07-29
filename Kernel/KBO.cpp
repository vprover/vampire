
/*
 * File KBO.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"
#include <fstream>

#include "Term.hpp"
#include "KBO.hpp"
#include "Signature.hpp"

#define COLORED_WEIGHT_BOOST 0x10000

namespace Kernel {

using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO* kbo)
    : _kbo(*kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  CLASS_NAME(KBO::State);
  USE_ALLOCATOR(State);

  void traverse(Term* t1, Term* t2);
  void traverse(TermList tl,int coefficient);
  Result result(Term* t1, Term* t2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList t1, TermList t2);
  Result applyVariableCondition(Result res)
  {
    if(_posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(_negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int _weightDiff;
  DHMap<unsigned, int, IdentityHash> _varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int _posNum;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result KBO::State::result(Term* t1, Term* t2)
{
  CALL("KBO::State::result")
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    if(t1->isLiteral()) {
      int prec1, prec2;
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else {
      res=_kbo.compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

  //the result should never be EQUAL:
  //- either t1 and t2 are truely equal. But then if they're equal, it
  //would have been discovered by the t1==t2 check in
  //KBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("KBO::State::innerResult");

  ASS_NEQ(tl1, tl2);
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
    } else {
      res=_kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    } else if(*pnum==1) {
      _posNum++;
    }
  } else {
    if(*pnum==0) {
      _posNum--;
    } else if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::State::traverse(TermList tl,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    _weightDiff += _kbo._funcWeights._variableWeight * coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.symbolWeight(t)*coef;

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      _weightDiff+=_kbo.symbolWeight(term)*coef;
      if(term->arity()) {
	stack.push(term->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      auto var = ts->var();
      _weightDiff += _kbo._funcWeights._variableWeight * coef;
      recordVariable(var, coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::State::traverse(Term* t1, Term* t2)
{
  CALL("KBO::State::traverse");
  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<TermList*> stack(32);
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!stack.isEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
	lexValidDepth=depth;
	if(_weightDiff!=0) {
	  _lexResult=_weightDiff>0 ? GREATER : LESS;
	}
	_lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      ASS(ss->term()->arity());
      stack.push(ss->term()->args());
      stack.push(tt->term()->args());
      depth++;
    } else {
      traverse(*ss,1);
      traverse(*tt,-1);
      if(_lexResult==EQUAL) {
	_lexResult=innerResult(*ss, *tt);
	lexValidDepth=depth;
	ASS(_lexResult!=EQUAL);
	ASS(_lexResult!=GREATER_EQ);
	ASS(_lexResult!=LESS_EQ);
      }
    }
  }
  ASS_EQ(depth,0);
}

struct PredSigTraits {
  static const char* symbolKindName() 
  { return "predicate"; }

  static unsigned nSymbols() 
  { return env.signature->predicates(); }

  static bool isColored(unsigned functor) 
  { return env.signature->predicateColored(functor);}

  static bool tryGetFunctor(const vstring& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetPredicateNumber(sym,arity, out); }

  static const vstring& weightFileName(const Options& opts) 
  { return opts.predicateWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return false; }

  static bool isConstantSymbol(unsigned functor) 
  { return false; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getPredicate(functor); } 
};


struct FuncSigTraits {
  static const char* symbolKindName() 
  { return "function"; }

  static unsigned nSymbols() 
  { return env.signature->functions(); } 

  static bool isColored(unsigned functor) 
  { return env.signature->functionColored(functor);}

  static bool tryGetFunctor(const vstring& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetFunctionNumber(sym,arity, out); }

  static const vstring& weightFileName(const Options& opts) 
  { return opts.functionWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return env.signature->getFunction(functor)->arity() == 1; } 

  static bool isConstantSymbol(unsigned functor) 
  { return env.signature->getFunction(functor)->arity() == 0; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getFunction(functor); } 
};

template<class SigTraits> 
KBO::WeightMap KBO::weightsFromOpts(const Options& opts) const {
  auto& str = SigTraits::weightFileName(opts);
  if (str.empty()) {
    return WeightMap::dflt<SigTraits>();
  } else if (str == "$random") {
    return WeightMap::randomized<SigTraits>(1 << 16, 
        [](unsigned min, unsigned max) { return min + Random::getInteger(max - min); });
  } else {
    return weightsFromFile<SigTraits>(opts);
  }
}

template<class SigTraits> KBO::WeightMap KBO::weightsFromFile(const Options& opts) const {
  DArray<KBO::Weight> weights(SigTraits::nSymbols());
  BYPASSING_ALLOCATOR

  ///////////////////////// parsing helper functions ///////////////////////// 
 
  /** opens the file with name f or throws a UserError on failure  */
  auto openFile = [](const vstring& f) -> ifstream {
    ifstream file(f.c_str());
    if (!file.is_open()) {
      throw UserErrorException("failed to open file ", f);
    }
    return file;
  };

#define SPECIAL_WEIGHT_IDENT_VAR            "$var"
#define SPECIAL_WEIGHT_IDENT_INTRODUCED     "$introduced"
#define SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT "$default"

  auto parseDefaultSymbolWeight = [&openFile](const vstring& fname) -> unsigned {
    if (!fname.empty()) {
      auto file = openFile(fname);
      for (vstring ln; getline(file, ln);) {
        unsigned dflt;
        vstring special_name;
        bool err = !(vstringstream(ln) >> special_name >> dflt);
        if (!err && special_name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) {
          return dflt;
        }
      }
    }
    return 1; // the default defaultSymbolWeight ;) 
  };

  /** tries to parse line of the form `<special_name> <weight>` */
  auto tryParseSpecialLine = [](const vstring& ln, unsigned& variableWeight, unsigned& introducedWeight) -> bool {
    vstringstream lnstr(ln);

    vstring name;
    unsigned weight;
    bool ok = !!(lnstr >> name >> weight);
    if (ok) {
           if (name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) { /* handled in parseDefaultSymbolWeight */ }
      else if (name == SPECIAL_WEIGHT_IDENT_VAR           ) { variableWeight   = weight; } 
      else if (name == SPECIAL_WEIGHT_IDENT_INTRODUCED    ) { introducedWeight = weight; } 
      else {
        throw Lib::UserErrorException("no special symbol with name '", name, "' (existing ones: " SPECIAL_WEIGHT_IDENT_VAR ", " SPECIAL_WEIGHT_IDENT_INTRODUCED " )");
      }
    }
    return ok;
  };

  /** tries to parse line of the form `<name> <arity> <weight>` */
  auto tryParseNormalLine = [&](const vstring& ln) -> bool {
    vstringstream lnstr(ln);

    vstring name;
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

  for (int i = 0; i < SigTraits::nSymbols(); i++) {
    weights[i] = SigTraits::isColored(i) 
          ? defaultSymbolWeight * COLORED_WEIGHT_BOOST 
          : defaultSymbolWeight;
  }

  unsigned introducedWeight = defaultSymbolWeight;
  unsigned variableWeight   = defaultSymbolWeight;

  ASS_REP(!filename.empty(), filename);

  auto file = openFile(filename);

  for (vstring ln; getline(file, ln);) {
    if (!tryParseNormalLine(ln) && !tryParseSpecialLine(ln, variableWeight, introducedWeight)) {
      throw Lib::UserErrorException(
             "failed to read line from file ",   filename, "\n",
             "expected syntax: '<name> <arity> <weight>'", "\n",
             "e.g.:            '$add   2       4       '", "\n",
             "or syntax: '<special_name> <weight>'"      , "\n",
             "e.g.:      '$var           7       '"      , "\n"
      );
    } 
  }

  return WeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._variableWeight         = variableWeight,
  };

}

KBO::KBO(
    // KBO params
    WeightMap funcWeights, 
    WeightMap predWeights, 

    // precedence ordering params
    DArray<int> funcPrec, 
    DArray<int> predPrec, 
    DArray<int> predLevels, 

    // other
    bool reverseLCM
  ) : PrecedenceOrdering(funcPrec, predPrec, predLevels, reverseLCM)
  , _funcWeights(funcWeights)
  , _predWeights(predWeights)
  , _state(new State(this))
{ 
  auto nFunctions = _funcWeights._weights.size();
  auto maximalFunctions = DArray<long int>(env.sorts->count());
  maximalFunctions.init(env.sorts->count(), -1);

  for (int i = 0; i < nFunctions; i++) {
    auto sort = env.signature->getFunction(i)->fnType()->result();
    /* register min function */
    auto maxFn = maximalFunctions[sort];
    if (maxFn == -1) {
      maximalFunctions[sort] = i;
    } else {
      if (compareFunctionPrecedences(maxFn, i)) {
        maximalFunctions[sort] = i;
      }
    }
  }

  ////////////////// check kbo-releated constraints //////////////////

  for (int i = 0; i < nFunctions; i++) {
    auto sort = env.signature->getFunction(i)->fnType()->result();
    auto arity = env.signature->getFunction(i)->arity();

    if (_funcWeights._weights[i] < _funcWeights._variableWeight && arity == 0) {
      throw UserErrorException("weight of constants must be greater or equal to the variable weight (", _funcWeights._variableWeight, ")");

    } else if (_funcWeights.symbolWeight(i) == 0 && arity == 1 && maximalFunctions[sort] != i) {
      throw UserErrorException( "a unary function of weight zero (i.e.: ", env.signature->getFunction(i)->name(), ") must be maximal wrt. the precedence ordering");

    }
  }

  if (_funcWeights._introducedSymbolWeight < _funcWeights._variableWeight) {
    throw UserErrorException("weight of introduced function symbols must be greater than the variable weight (= ", _funcWeights._variableWeight, "), since there might be new constant symbols introduced during proof search.");
  }

  if (_funcWeights._variableWeight <= 0) {
    throw new UserErrorException("variable weight must be greater than zero");
  }
}

/**
 * Create a KBO object.
 */
KBO::KBO(Problem& prb, const Options& opts)
 : PrecedenceOrdering(prb, opts)
 , _funcWeights(weightsFromOpts<FuncSigTraits>(opts))
 , _predWeights(weightsFromOpts<PredSigTraits>(opts))
 , _state(new State(this))
{
  CALL("KBO::KBO(Prb&, Opts&)");
}

KBO::~KBO()
{
  CALL("KBO::~KBO");

  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::comparePredicates(Literal* l1, Literal* l2) const
{
  CALL("KBO::comparePredicates");
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  Result res;
  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif
  state->init();
  if(p1!=p2) {
    TermList* ts;
    ts=l1->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,1);
      ts=ts->next();
    }
    ts=l2->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,-1);
      ts=ts->next();
    }
  } else {
    state->traverse(l1,l2);
  }

  res=state->result(l1,l2);
#if VDEBUG
  _state=state;
#endif
  return res;
} // KBO::comparePredicates()

Ordering::Result KBO::compare(TermList tl1, TermList tl2) const
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
  }
  if(tl2.isOrdinaryVar()) {
    return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(t1->functor()==t2->functor()) {
    state->traverse(t1,t2);
  } else {
    state->traverse(tl1,1);
    state->traverse(tl2,-1);
  }
  Result res=state->result(t1,t2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

int KBO::symbolWeight(Term* t) const
{
  return (t->isLiteral() ? _predWeights
                         : _funcWeights ).symbolWeight(t);
}

template<class SigTraits>
KBO::WeightMap KBO::WeightMap::dflt()
{
  return WeightMap {
    ._weights                = DArray<Weight>::initialized(SigTraits::nSymbols(), 1),
    ._introducedSymbolWeight = 1,
    ._variableWeight         = 1,
  };
}

template<class SigTraits, class Random>
KBO::WeightMap KBO::WeightMap::randomized(unsigned maxWeight, Random random)
{
  auto nSym = SigTraits::nSymbols();

  unsigned variableWeight   = random(1,              maxWeight);
  unsigned introducedWeight = random(variableWeight, maxWeight);

  DArray<KBO::Weight> weights(nSym);
  for (int i = 0; i < nSym; i++) {
    if (SigTraits::isConstantSymbol(i)) {
      weights[i] = random(variableWeight, maxWeight);
    } else if (SigTraits::isUnaryFunction(i)) {
      // TODO support one zero-weight-unary-function per sort
      weights[i] = random(1, maxWeight); 
    } else {
      weights[i] = random(0, maxWeight);
    }
  }

  return WeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._variableWeight         = variableWeight,
  };
}

KBO::Weight KBO::WeightMap::symbolWeight(Term* t) const 
{
  return symbolWeight(t->functor());
}

KBO::Weight KBO::WeightMap::symbolWeight(unsigned functor) const 
{
  if (functor >= _weights.size()) {
    /* symbol introduced during proof search */
    return _introducedSymbolWeight;
  } else {
    return _weights[functor];
  }
}

template<class SigTraits>
void KBO::showConcrete_(ostream& out) const  
{
  out << "% ===== begin of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;

  for (int i = 0; i < SigTraits::nSymbols(); i++) {
    auto sym = SigTraits::getSymbol(i);
    out << "% " << sym->name() << " " << sym->arity() << " " << getWeightMap<SigTraits>().symbolWeight(i) << std::endl;
  }

  out << "% ===== end of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;

}
void KBO::showConcrete(ostream& out) const  
{
  showConcrete_<FuncSigTraits>(out);
  out << "%" << std::endl;
  showConcrete_<PredSigTraits>(out);
}

template<> const KBO::WeightMap& KBO::getWeightMap<FuncSigTraits>() const 
{ return _funcWeights; }

template<> const KBO::WeightMap& KBO::getWeightMap<PredSigTraits>() const 
{ return _predWeights; }

}
