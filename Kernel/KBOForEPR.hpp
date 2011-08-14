/**
 * @file KBOForEPR.hpp
 * Defines class KBOForEPR for instances of the Knuth-Bendix ordering for EPR problems
 */

#ifndef __KBOForEPR__
#define __KBOForEPR__

#include "Forwards.hpp"

#include "KBO.hpp"

namespace Kernel {

using namespace Lib;

/**
 * Class for instances of the Knuth-Bendix orderings
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBOForEPR
: public KBOBase
{
public:
  KBOForEPR(Problem& prb, const Options& opt);

  virtual Result compare(Literal* l1, Literal* l2) const;
  virtual Result compare(TermList tl1, TermList tl2) const;
};

}
#endif
