
/*
 * File KBO.hpp.
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

namespace Kernel {

using namespace Lib;

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

  using Weight = unsigned;

  struct WeightMap {
    friend class KBO;
    DArray<Weight> _weights;

    /** Weight of function symbols not occurring in the signature, i.e. that are introduced during proof search */
    Weight _introducedSymbolWeight;

    /** Weight of variables 
     * (note: this field is dead code for the WeightMap '_predWeights', and only present since it makes the 
     * parsing and initializing code more uniform, and therefore simpler) 
     */
    const Weight _variableWeight;


    Weight symbolWeight(Term*    t      ) const;
    Weight symbolWeight(unsigned functor) const;

  private:
    template<class SigTraits              > static WeightMap dflt();
    template<class SigTraits, class Random> static WeightMap randomized(unsigned maxWeight, Random random);
  };

  KBO(Problem& prb, const Options& opt);
  KBO(
      // KBO params
      WeightMap funcWeights, 
      WeightMap predWeights, 

      // precedence ordering params
      DArray<int> funcPrec, 
      DArray<int> predPrec, 
      DArray<int> predLevels,

      // other
      bool reverseLCM);

  virtual ~KBO();
  void showConcrete(ostream&) const override;

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;
protected:
  Result comparePredicates(Literal* l1, Literal* l2) const override;


  class State;

  // int functionSymbolWeight(unsigned fun) const;
  int symbolWeight(Term* t) const;

private:

  WeightMap _funcWeights;
  WeightMap _predWeights;

  template<class SigTraits> const WeightMap& getWeightMap() const;
  template<class SigTraits> WeightMap weightsFromOpts(const Options& opts) const;
  template<class SigTraits> WeightMap weightsFromFile(const Options& opts) const;
  template<class SigTraits> 
  void showConcrete_(ostream&) const;

  /**
   * State used for comparing terms and literals
   */
  mutable State* _state;
};

}
#endif
