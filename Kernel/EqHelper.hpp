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
 * @file EqHelper.hpp
 * Defines class EqHelper.
 */


#ifndef __EqHelper__
#define __EqHelper__

#include "Forwards.hpp"

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/DHSet.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

class EqHelper
{
public:
  static TermList getOtherEqualitySide(Literal* eq, TermList lhs);
  static bool hasGreaterEqualitySide(Literal* eq, const Ordering& ord, TermList& lhs, TermList& rhs);
  static VirtualIterator<Term*> getSubtermIterator(Literal* lit, const Ordering& ord);
#if VHOL
  static VirtualIterator<Term*> getFoSubtermIterator(Literal* lit, const Ordering& ord);
  static TermIterator getBooleanSubtermIterator(Literal* lit, const Ordering& ord);  
#endif  
  static TermIterator getLHSIterator(Literal* lit, const Ordering& ord);
  static TermIterator getSuperpositionLHSIterator(Literal* lit, const Ordering& ord, const Options& opt);
  static TermIterator getDemodulationLHSIterator(Literal* lit, bool forward, const Ordering& ord, const Options& opt);
  static TermIterator getEqualityArgumentIterator(Literal* lit);

  struct LHSIteratorFn
  {
    LHSIteratorFn(const Ordering& ord) : _ord(ord) {}

    VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
    {
      return pvi( pushPairIntoRightIterator(lit, getLHSIterator(lit, _ord)) );
    }
  private:
    const Ordering& _ord;
  };

  struct SuperpositionLHSIteratorFn
  {
    SuperpositionLHSIteratorFn(const Ordering& ord, const Options& opt) : _ord(ord), _opt(opt) {}

    VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
    {
      return pvi( pushPairIntoRightIterator(lit, getSuperpositionLHSIterator(lit, _ord, _opt)) );
    }
  private:
    const Ordering& _ord;
    const Options& _opt;
  };

  struct EqualityArgumentIteratorFn
  {
    VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
    {
      return pvi( pushPairIntoRightIterator(lit, getEqualityArgumentIterator(lit)) );
    }
  };

  static bool isEqTautology(Literal* lit)
  {
    return lit->isEquality() && lit->isPositive() && (*lit->nthArgument(0))==(*lit->nthArgument(1));
  }
private:

  template<class SubtermIterator>
  static VirtualIterator<ELEMENT_TYPE(SubtermIterator)> getRewritableSubtermIterator(Literal* lit, const Ordering& ord);

  struct IsNonVariable;

};

};

#endif /* __EqHelper__ */
