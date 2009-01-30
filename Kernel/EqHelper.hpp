/**
 * @file EqHelper.hpp
 * Defines class EqHelper.
 */


#ifndef __EqHelper__
#define __EqHelper__

#include "../Forwards.hpp"

#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Metaiterators.hpp"
#include "../Lib/PairUtils.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

class EqHelper
{
public:
  static TermList getRHS(Literal* eq, TermList lhs);
  static TermIterator getRewritableSubtermIterator(Literal* lit);
  static TermIterator getLHSIterator(Literal* lit);
  static TermIterator getEqualityArgumentIterator(Literal* lit);

  static Literal* replace(Literal* lit, TermList what, TermList by);

  struct LHSIteratorFn
  {
    DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      return pvi( pushPairIntoRightIterator(lit, getLHSIterator(lit)) );
    }
  };

  struct EqualityArgumentIteratorFn
  {
    DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
    OWN_RETURN_TYPE operator()(Literal* lit)
    {
      return pvi( pushPairIntoRightIterator(lit, getEqualityArgumentIterator(lit)) );
    }
  };

};

};

#endif /* __EqHelper__ */
