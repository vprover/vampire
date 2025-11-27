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
 * @file SortInference.hpp
 * Defines class SortInference.
 *
 *
 * NOTE: An important convention to remember is that when we have a DArray representing
 *       the signature or grounding of a function the last argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
 */

#ifndef __SortInference__
#define __SortInference__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

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

    // for each distinct sort gives a sort that can be used for variable equalities that are otherwise unsorted
    // some of these will not be used, we could detect these cases... but it is not interesting
    DArray<unsigned> varEqSorts;

    // the distinct parents of sorts
    // has length sorts with contents from distinctSorts
    // invariant: all monotonic sorts will have parent 0, the first non-monotonic sort
    DArray<unsigned> parents;

    // Map the distinct sorts back to their vampire parents
    // A distinct sort may merge multiple vampire sorts (due to monotonicity)
    DHMap<unsigned,Stack<unsigned>*> distinctToVampire;
    // A vampire sort can only be mapped to more than one distinct sort under certain conditions i.e. when
    // (i) the option for fmbSortInference = expand
    // (ii) at most one sort has non-monotonic subsorts and that is called parent
    // (iii) additional constraints have been added making expanded <= parent
    DHMap<unsigned,Stack<unsigned>*> vampireToDistinct;
    // This maps to the distinct parent
    // invariant: domain of the two maps are the same and the second maps to something in the stack of the first
    DHMap<unsigned,unsigned> vampireToDistinctParent;

    // has size distinctSorts
    // is 1 if that distinct sort is monotonic
    ZIArray<bool> monotonicSorts;
};

class SortInference {
public:
  SortInference(ClauseList* clauses,
                const DArray<bool>& del_f,
                const DArray<bool>& del_p,
                Stack<std::pair<unsigned,unsigned>>& distinct_sort_constraints,
                DHMap<unsigned,DArray<signed char>*>& monotonic_vampire_sorts) :
                _clauses(clauses), _del_f(del_f), _del_p(del_p),
                // these two are essentially output arguments
                _sort_constraints(distinct_sort_constraints),
                _monotonic_vampire_sorts(monotonic_vampire_sorts)
                {
                  _sig = new SortedSignature();
                  _print = env.options->showFMBsortInfo();

                   // ignore inference if there are no clauses
                  _ignoreInference = !clauses;
                  _expandSubsorts = env.options->fmbAdjustSorts() == Options::FMBAdjustSorts::EXPAND;

                  _usingMonotonicity = true;
                  _collapsingMonotonicSorts = (env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::OFF &&
                                               env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::EXPAND);
                  _assumeMonotonic = _collapsingMonotonicSorts &&
                                     env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::GROUP;

                  _distinctSorts=0;
                  _collapsed=0;

                  ASS(! (_expandSubsorts && _collapsingMonotonicSorts) );
                  ASS( _collapsingMonotonicSorts || !_assumeMonotonic);
                }

   void doInference();

   SortedSignature* getSignature(){ return _sig; }

private:

   unsigned getDistinctSort(unsigned subsort, unsigned vampireSort, bool createNew=true);

  bool _print;
  bool _ignoreInference;
  bool _expandSubsorts;
  bool _usingMonotonicity;
  bool _collapsingMonotonicSorts;
  bool _assumeMonotonic;

  unsigned _distinctSorts;
  unsigned _collapsed;
  ZIArray<unsigned> _posEqualitiesOnSort;  // grows as needed, as new sorts are named

  SortedSignature* _sig;
  ClauseList* _clauses;
  const DArray<bool>& _del_f;
  const DArray<bool>& _del_p;

  // these two actually live in FiniteModelBuilder and serve as output arguments of this sort inference
  // (see more explanations there)
  Stack<std::pair<unsigned,unsigned>>& _sort_constraints;
  DHMap<unsigned,DArray<signed char>*>& _monotonic_vampire_sorts;
};

}

#endif // __SortInference__
