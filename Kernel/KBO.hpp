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
 * @file KBO.hpp
 * Defines class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#ifndef __KBO__
#define __KBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Hash.hpp"
#include "Lib/DHMap.hpp"

#include "Ordering.hpp"

#define SPECIAL_WEIGHT_IDENT_VAR            "$var"
#define SPECIAL_WEIGHT_IDENT_INTRODUCED     "$introduced"
#define SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT "$default"
#define SPECIAL_WEIGHT_IDENT_NUM_INT        "$int"
#define SPECIAL_WEIGHT_IDENT_NUM_RAT        "$rat"
#define SPECIAL_WEIGHT_IDENT_NUM_REAL       "$real"

#define __KBO__CUSTOM_PREDICATE_WEIGHTS__ 1

namespace Kernel {

using namespace Lib;

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
struct PredSigTraits;
#endif
struct FuncSigTraits;


using KboWeight = unsigned;

/** 
 * Contains special weights for, variables and interpreted functions for SigTraits == FuncSigTraits, 
 * and nothing for SigTraits == PredSigTraits 
 */
template<class SigTraits>
struct KboSpecialWeights;

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__

template<>
struct KboSpecialWeights<PredSigTraits> 
{ 
  inline bool tryAssign(const vstring& name, unsigned weight) 
  { return false; }

  inline static KboSpecialWeights dflt(bool qkbo) 
  { return { }; }

  bool tryGetWeight(unsigned functor, unsigned& weight) const;
};

#endif

template<>
struct KboSpecialWeights<FuncSigTraits> 
{
  KboWeight _variableWeight;
  KboWeight _numInt;
  KboWeight _numRat;
  KboWeight _numReal;
  bool _qkbo;
  inline bool tryAssign(const vstring& name, unsigned weight) 
  {
    if (name == SPECIAL_WEIGHT_IDENT_VAR     ) { _variableWeight = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_INT ) { _numInt  = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_REAL) { _numReal = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_RAT ) { _numRat  = weight; return true; } 
    return false;
  }

  inline static KboSpecialWeights dflt(bool qkbo) 
  { 
    return { 
      ._variableWeight = 1, 
      ._numInt  = 1,
      ._numRat  = 1,
      ._numReal = 1,
      ._qkbo = qkbo,
    }; 
  }

  bool tryGetWeight(unsigned functor, unsigned& weight) const;
};


template<class SigTraits>
struct KboWeightMap {
  friend class KBO;
  DArray<KboWeight> _weights;

  /** KboWeight of function symbols not occurring in the signature, i.e. that are introduced during proof search */
  KboWeight _introducedSymbolWeight;

  /** Special weights that are only present for function/predicate symbols. */
  KboSpecialWeights<SigTraits> _specialWeights;

  KboWeight symbolWeight(Term*    t      ) const;
  KboWeight symbolWeight(unsigned functor) const;

  static KboWeightMap dflt(bool qkbo);
  template<class Extractor, class Fml>
  static KboWeightMap fromSomeUnsigned(Extractor ex, Fml fml, bool qkbo);

private:
  static KboWeightMap randomized(bool qkbo);
  template<class Random> static KboWeightMap randomized(unsigned maxWeight, Random random, bool qkbo);
};

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
: public PrecedenceOrdering
{
public:
  CLASS_NAME(KBO);
  USE_ALLOCATOR(KBO);

  KBO(KBO&&) = default;
  KBO& operator=(KBO&&) = default;
  KBO(Problem& prb, const Options& opt, bool qkboPrecedence = false);
  KBO(
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
      bool reverseLCM,
      bool qkboPrecedence = false);

  static KBO testKBO(bool randomized = true, bool qkboPrecedence = false);

  virtual ~KBO();
  void showConcrete(ostream&) const override;
  template<class HandleError>
  void checkAdmissibility(HandleError handle) const;
  void zeroWeightForMaximalFunc();

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;

  /* compares the function precedences of the top symbols of the term/literal/sort t1, t2 
   */
  Result comparePrecedence(Term* t1, Term* t2) const;
protected:
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  int predicateWeight(unsigned t) const;
#endif
  int functionWeight(unsigned t) const;
  int variableWeight() const;
  Result comparePredicates(Literal* l1, Literal* l2) const override;


  /**
   * Class to represent the current state of the KBO comparison.
   * @since 30/04/2008 flight Brussels-Tel Aviv
   */
  class State
  {
  public:
    /** Initialise the state */
    State()
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

    void traverse(KBO const& kbo, Term* t1, Term* t2);
    void traverse(KBO const& kbo, TermList tl,int coefficient);
    Result result(KBO const& kbo, Term* t1, Term* t2);
  private:
    void recordVariable(unsigned var, int coef);
    Result innerResult(KBO const& kbo, TermList t1, TermList t2);
    Result applyVariableCondition(Result res);
    

    int _weightDiff;
    DHMap<unsigned, int, IdentityHash> _varDiffs;
    /** Number of variables, that occur more times in the first literal */
    int _posNum;
    /** Number of variables, that occur more times in the second literal */
    int _negNum;
    /** First comparison result */
    Result _lexResult;
    /** The variable counters */
  }; // class State



private:
  int symbolWeight(Term* t) const;

  template<class SigTraits> const KboWeightMap<SigTraits>& getWeightMap() const;
  template<class SigTraits> static KboWeightMap<SigTraits> weightsFromOpts(const Options& opts, const DArray<int>& rawPrecedence, bool qkbo);
  template<class SigTraits> static KboWeightMap<SigTraits> weightsFromFile(const Options& opts, bool qkbo);

  template<class SigTraits> 
  void showConcrete_(ostream&) const;

  KboWeightMap<FuncSigTraits> _funcWeights;
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  KboWeightMap<PredSigTraits> _predWeights;
#endif
  /**
   * State used for comparing terms and literals
   */
  mutable unique_ptr<State> _state;
};

}
#endif
