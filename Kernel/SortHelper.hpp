/**
 * @file SortHelper.hpp
 * Defines class SortHelper.
 */

#ifndef __SortHelper__
#define __SortHelper__

#include "Forwards.hpp"

namespace Kernel {

class SortHelper {
public:
  static unsigned getResultSort(Term* t);
  static unsigned getArgSort(Term* t, unsigned argIndex);

  static unsigned getEqualityArgumentSort(Literal* lit);
  static unsigned getArgSort(Literal* lit, unsigned argIndex);
};

}

#endif // __SortHelper__
