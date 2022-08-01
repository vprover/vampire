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

#ifndef __SKIKBO__
#define __SKIKBO__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/SmartPtr.hpp"

#include "KBO.hpp"
#include "Ordering.hpp"
#include "Signature.hpp"
#include "TermIterators.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class SKIKBO
: public PrecedenceOrdering
{
public:
  CLASS_NAME(SKIKBO);
  USE_ALLOCATOR(SKIKBO);

  SKIKBO(Problem& prb, const Options& opt, bool basic_hol = false);
  SKIKBO(
        // KBO params
        KboWeightMap<FuncSigTraits> symbolWeights, 

        // precedence ordering params
        DArray<int> funcPrec, 
        DArray<int> typeConPrec,
        // pred prec and pred levels are useless
        // as in higher-order we treat all symbol as function symbols (or type cons)
        DArray<int> predPrec, 
        DArray<int> predLevels,

        // other
        bool reverseLCM);

  virtual ~SKIKBO();

  typedef SmartPtr<ApplicativeArgsIt> ArgsIt_ptr;

  using PrecedenceOrdering::compare;
  Result compare(TermList tl1, TermList tl2) const override;
  static unsigned maximumReductionLength(Term* t);
  static TermList reduce(TermStack& args, TermList& head);

protected:
  typedef DHMap<unsigned, DArray<DArray<unsigned>*>*> VarOccMap;

  //Result comparePredicates(Literal* l1, Literal* l2) const override;

  enum VarCondRes {
    INCOMP,
    LEFT,
    RIGHT,
    BOTH
  };
 
  class State;

  Result comparePredicates(Literal* l1, Literal* l2) const override
  {
    return Ordering::INCOMPARABLE;
  }

  void showConcrete(ostream&) const override
  { NOT_IMPLEMENTED; }

  //VarCondRes compareVariables(VarOccMap&, VarOccMap&, VarCondRes) const;
  VarCondRes compareVariables(TermList tl1, TermList tl2) const;
  unsigned getMaxRedLength(TermList t) const;
  bool varConditionHolds(DHMultiset<Term*>& tlTerms1, DHMultiset<Term*>& tlTerms2) const;
  bool safe(Term* t1, Term* t2) const;

  /** Weight of variables */
  int _variableWeight;
  /** Weight of function symbols not occurring in the
   * signature */
  int _defaultSymbolWeight;

  KboWeightMap<FuncSigTraits> _weights;

  int symbolWeight(Term* t) const;

  bool allConstantsHeavierThanVariables() const { return false; }
  bool existsZeroWeightUnaryFunction() const { return false; }
  bool sameCategoryHeads(ArgsIt_ptr a1, ArgsIt_ptr a2) const
  {
    return a1->varHead() == a2->varHead();
  }
  mutable State* _state;
  bool _basic_hol;

#if VDEBUG
  static vstring vCondResToString(VarCondRes v)
  {
    if(v == INCOMP){ return "incomparable"; }
    if(v == LEFT){ return "left"; }
    if(v == RIGHT){ return "right"; }
    if(v == BOTH){ return "both"; }
    return "none"; // just to suppress a warning
  }
#endif


};

}
#endif
