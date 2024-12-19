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

#include "Ordering.hpp"

#define SPECIAL_WEIGHT_IDENT_VAR            "$var"
#define SPECIAL_WEIGHT_IDENT_INTRODUCED     "$introduced"
#define SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT "$default"
#define SPECIAL_WEIGHT_IDENT_NUM_INT        "$int"
#define SPECIAL_WEIGHT_IDENT_NUM_RAT        "$rat"
#define SPECIAL_WEIGHT_IDENT_NUM_REAL       "$real"

#define __KBO__CUSTOM_PREDICATE_WEIGHTS__ 0

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
  inline bool tryAssign(const std::string& name, unsigned weight) 
  { return false; }

  inline static KboSpecialWeights dflt() 
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
  inline bool tryAssign(const std::string& name, unsigned weight) 
  {
    if (name == SPECIAL_WEIGHT_IDENT_VAR     ) { _variableWeight = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_INT ) { _numInt  = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_REAL) { _numReal = weight; return true; } 
    if (name == SPECIAL_WEIGHT_IDENT_NUM_RAT ) { _numRat  = weight; return true; } 
    return false;
  }

  inline static KboSpecialWeights dflt() 
  { 
    return { 
      ._variableWeight = 1, 
      ._numInt  = 1,
      ._numRat  = 1,
      ._numReal = 1,
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

  KboWeight symbolWeight(const Term* t) const;
  KboWeight symbolWeight(unsigned functor) const;

  static KboWeightMap dflt();
  template<class Extractor, class Fml>
  static KboWeightMap fromSomeUnsigned(Extractor ex, Fml fml);
private:
  static KboWeightMap randomized();
  template<class Random> static KboWeightMap randomized(unsigned maxWeight, Random random);
};

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO
: public PrecedenceOrdering
{
public:
  KBO(Problem& prb, const Options& opt);
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
      bool reverseLCM);

  static KBO testKBO();

  virtual ~KBO();
  void showConcrete(std::ostream&) const override;
  template<class HandleError>
  void checkAdmissibility(HandleError handle) const;
  void zeroWeightForMaximalFunc();

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;

  Result compare(AppliedTerm t1, AppliedTerm t2, POStruct* po_struct = nullptr) const override;
  Result isGreaterOrEq(AppliedTerm t1, AppliedTerm t2) const override;
  OrderingComparatorUP createComparator(bool onlyVars = false) const override;

protected:
  unsigned computeWeight(AppliedTerm tt) const;

  Result comparePredicates(Literal* l1, Literal* l2) const override;

  friend struct OrderingComparator;
  friend class KBOComparator;

  // int functionSymbolWeight(unsigned fun) const;
  int symbolWeight(const Term* t) const;

private:

  KboWeightMap<FuncSigTraits> _funcWeights;
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  KboWeightMap<PredSigTraits> _predWeights;
#endif

  template<class SigTraits> const KboWeightMap<SigTraits>& getWeightMap() const;
  template<class SigTraits> KboWeightMap<SigTraits> weightsFromOpts(const Options& opts, const DArray<int>& rawPrecedence) const;
  template<class SigTraits> KboWeightMap<SigTraits> weightsFromFile(const Options& opts) const;

  template<class SigTraits> 
  void showConcrete_(std::ostream&) const;

  /**
   * Class to represent the current state of the KBO comparison.
   * Based on Bernd Loechner's "Things to Know when Implementing KBO"
   * (https://doi.org/10.1007/s10817-006-9031-4)
   * @since 30/04/2008 flight Brussels-Tel Aviv
   */
  class State
  {
  public:
    /** Initialise the state */
    State(const KBO* kbo)
      : _kbo(*kbo)
    {}

    void init(POStruct* po_struct = nullptr)
    {
      _weightDiff=0;
      _posNum=0;
      _negNum=0;
      _lexResult=EQUAL;
      _varDiffs.reset();
      _po_struct=po_struct;
    }

    /**
     * Lexicographic traversal of two terms with same top symbol,
     * i.e. traversing their symbols in lockstep, as descibed in
     * the Loechner et al. paper above. It performs a bidirectional
     * comparison between the two terms, i.e. we can get any value
     * of @b Result.
     */
    Result traverseLexBidir(AppliedTerm t1, AppliedTerm t2);
    /**
     * Optimised, unidirectional version of @b traverseLexBidir
     * where we only care about @b GREATER and @b EQUAL, otherwise
     * it returns as early as possible with @b INCOMPARABLE.
     */
    Result traverseLexUnidir(AppliedTerm t1, AppliedTerm t2);
    /**
     * Performs a non-lexicographic (i.e. non-lockstep) traversal
     * of two terms in case their top symbols are not the same.
     */
    template<bool unidirectional>
    Result traverseNonLex(AppliedTerm t1, AppliedTerm t2);

    template<int coef, bool varsOnly> void traverse(AppliedTerm tt);

    Result result(AppliedTerm t1, AppliedTerm t2);
  protected:
    template<int coef> void recordVariable(unsigned var);

    bool checkVars() const { return _negNum <= 0; }
    Result innerResult(TermList t1, TermList t2);
    Result applyVariableCondition(Result res)
    {
      if(_posNum>0 && (res==LESS || res==EQUAL)) {
        res=INCOMPARABLE;
      } else if(_negNum>0 && (res==GREATER || res==EQUAL)) {
        res=INCOMPARABLE;
      }
      return res;
    }

    friend class KBOComparator;

    int _weightDiff;
    /** The variable counters */
    DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
    /** Number of variables, that occur more times in the first literal */
    int _posNum;
    /** Number of variables, that occur more times in the second literal */
    int _negNum;
    /** First comparison result */
    Result _lexResult;
    /** The ordering used */
    const KBO& _kbo;
    POStruct* _po_struct;
  }; // class KBO::State

  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
};

}
#endif
