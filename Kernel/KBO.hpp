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
  inline bool tryAssign(const vstring& name, unsigned weight) 
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
  inline bool tryAssign(const vstring& name, unsigned weight) 
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

  KboWeight symbolWeight(Term*    t      ) const;
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
  bool isGreater(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, const Indexing::TermQueryResult* qr) const override;
  bool makeGreater(TermList tl1, TermList tl2, VarOrder& vo) const override;
  bool isGreater(TermList tl1, TermList tl2, const VarOrder& vo) const override;

  void* createState() const override;
  void initStateForTerm(void* state, Term* t) const override;
  void destroyState(void* state) const override;

  KboWeightMap<FuncSigTraits> _funcWeights;
protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;

  class State;
  class StateGreater;
  class StateGreaterVO;
  class StateGreaterSubst;

  // int functionSymbolWeight(unsigned fun) const;
  int symbolWeight(Term* t) const;
  void computeWeight(Term* t) const;
  void computeWeight2(Term* t, Indexing::ResultSubstitution* subst) const;
  bool weightsOk(TermList lhs, TermList rhs) const;
  unsigned weight(TermList t) const;
  unsigned weight2(TermList t, Indexing::ResultSubstitution* subst, bool underSubst) const;

private:
  bool isGreaterHelper(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, VarOrderBV* newConstraints) const;
  bool isGreaterHelper(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, VarOrderBV* newConstraints, Indexing::ResultSubstitution* subst, bool weightsEqual) const;
  bool makeGreaterNonRecursive(TermList tl1, TermList tl2, VarOrder& vo) const;
  bool makeGreaterRecursive(TermList tl1, TermList tl2, VarOrder& vo) const;

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  KboWeightMap<PredSigTraits> _predWeights;
#endif

  template<class SigTraits> const KboWeightMap<SigTraits>& getWeightMap() const;
  template<class SigTraits> KboWeightMap<SigTraits> weightsFromOpts(const Options& opts, const DArray<int>& rawPrecedence) const;
  template<class SigTraits> KboWeightMap<SigTraits> weightsFromFile(const Options& opts) const;

  template<class SigTraits> 
  void showConcrete_(std::ostream&) const;

  // struct DemodulatorConstraints {
  //   bool canDecompose = false;
  //   Stack<std::tuple<unsigned,unsigned,bool>> constraints;
  // };

  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
  mutable StateGreater* _stateGt;
  mutable StateGreaterVO* _stateGtVo;
  mutable StateGreaterSubst* _stateGtSubst;
  // mutable DHMap<std::pair<TermList,Literal*>,DemodulatorConstraints> _demodulatorCache;
};

}
#endif