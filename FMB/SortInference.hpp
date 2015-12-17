/**
 * @file SortInference.hpp
 * Defines class SortInference.
 *
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the signature or grounding of a function the lastt argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
 */

#ifndef __SortInference__
#define __SortInference__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Kernel/Signature.hpp"

namespace FMB {
using namespace Kernel;
using namespace Shell;
using namespace Lib;


struct SortedSignature{
    unsigned sorts;
    DArray<Stack<unsigned>> sortedConstants;
    DArray<Stack<unsigned>> sortedFunctions;

    // for f(x,y) = z this will store sort(z),sort(x),sort(y)
    DArray<DArray<unsigned>> functionSignatures;
    // for p(x,y) this will store sort(x),sort(y)
    DArray<DArray<unsigned>> predicateSignatures;

    // gives the maximum size of a sort
    DArray<unsigned> sortBounds;
    
    // the number of distinct sorts that might have different sizes
    unsigned distinctSorts;

    // the distinct parents of sorts
    // has length sorts with contents from distinctSorts
    // invariant: all monotonic sorts will have parent 0, the first non-monotonic sort
    DArray<unsigned> parents;
};

class SortInference {
public:
  CLASS_NAME(SortInference);
  USE_ALLOCATOR(SortInference);    
  
  static SortedSignature*  apply(ClauseIterator cit,
                                 DArray<unsigned> del_f,
                                 DArray<unsigned> del_p);

};

}

#endif // __SortInference__
