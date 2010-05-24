/**
 * @file MLVariant.hpp
 * Defines class MLVariant with methods
 * supporting multiliteral variant testing.
 */


#ifndef __MLVariant__
#define __MLVariant__

#include "Forwards.hpp"

namespace Kernel {

using namespace Lib;

class MLVariant {
public:
  static bool isVariant(Literal** cl1Lits, Clause* cl2, LiteralList** alts);
  static bool isVariant(Literal** cl1Lits, Clause* cl2, bool complementary=false);
  static bool isVariant(Clause* cl1, Clause* cl2, bool complementary=false)
  {
    return cl1->length()==cl2->length() && isVariant(cl1->literals(), cl2, complementary);
  }

};


};

#endif /* __MLVariant__ */
