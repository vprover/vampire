/**
 * @file TermTransformer.hpp
 * Defines class TermTransformer.
 */

#ifndef __TermTransformer__
#define __TermTransformer__

#include "Forwards.hpp"



namespace Kernel {

class TermTransformer {
public:
  Literal* transform(Literal* lit);
protected:
  virtual TermList transform(TermList trm) = 0;
};

}

#endif // __TermTransformer__
