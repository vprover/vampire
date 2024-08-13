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
 *       the signature or grounding of a function the lastt argument is the return
 *       so array[arity] is return and array[i] is the ith argument of the function
 */

#ifndef __SortInference__
#define __SortInference__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/IntUnionFind.hpp"
#include "Kernel/Signature.hpp"

namespace FMB {
using namespace Kernel;
using namespace Shell;

struct SortedSignature{
    unsigned sorts;
    Lib::DArray<Lib::Stack<unsigned>> sortedConstants;
    Lib::DArray<Lib::Stack<unsigned>> sortedFunctions;

    // for f(x,y) = z this will store sort(z),sort(x),sort(y)
    Lib::DArray<Lib::DArray<unsigned>> functionSignatures;
    // for p(x,y) this will store sort(x),sort(y)
    Lib::DArray<Lib::DArray<unsigned>> predicateSignatures;

    // gives the maximum size of a sort
    Lib::DArray<unsigned> sortBounds;
    
    // the number of distinct sorts that might have different sizes
    unsigned distinctSorts;

    // for each distinct sort gives a sort that can be used for variable equalities that are otherwise unsorted
    // some of these will not be used, we could detect these cases... but it is not interesting
    Lib::DArray<unsigned> varEqSorts;

    // the distinct parents of sorts
    // has length sorts with contents from distinctSorts
    // invariant: all monotonic sorts will have parent 0, the first non-monotonic sort
    Lib::DArray<unsigned> parents;

    // Map the distinct sorts back to their vampire parents
    // A distinct sort may merge multipe vampire sorts (due to monotonicity)
    Lib::DHMap<unsigned,Lib::Stack<unsigned>*> distinctToVampire;
    // A vampire sort can only be mapped to more than one distinct sort under certain conditions i.e. when
    // (i) the option for fmbSortInference = expand
    // (ii) at most one sort has non-monotonic subsorts and that is called parent
    // (iii) additional constraints have been added making expanded <= parent
    Lib::DHMap<unsigned,Lib::Stack<unsigned>*> vampireToDistinct;
    // This maps to the distinct parent
    // invariant: domain of the two maps are the same and the second maps to something in the stack of the first
    Lib::DHMap<unsigned,unsigned> vampireToDistinctParent;

    // has size distinctSorts
    // is 1 if that distinct sort is monotonic
    Lib::ZIArray<bool> monotonicSorts;
};

class SortInference {
public:
  SortInference(ClauseList* clauses,
                Lib::DArray<unsigned> del_f,
                Lib::DArray<unsigned> del_p,
                Lib::Stack<Lib::DHSet<unsigned>*> equiv_v_sorts,
                Lib::Stack<std::pair<unsigned,unsigned>>& cons) :
                _clauses(clauses), _del_f(del_f), _del_p(del_p),
                _equiv_v_sorts(equiv_v_sorts), _equiv_vs(Lib::env.signature->typeCons()),
                _sort_constraints(cons) {

                  _sig = new SortedSignature();
                  _print = Lib::env.options->showFMBsortInfo();

                   // ignore inference if there are no clauses
                  _ignoreInference = !clauses; 
                  _expandSubsorts = Lib::env.options->fmbAdjustSorts() == Options::FMBAdjustSorts::EXPAND;

                  _usingMonotonicity = true;
                  _collapsingMonotonicSorts = (Lib::env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::OFF && 
                                               Lib::env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::EXPAND);
                  _assumeMonotonic = _collapsingMonotonicSorts && 
                                     Lib::env.options->fmbAdjustSorts() != Options::FMBAdjustSorts::GROUP;

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
  Lib::DHSet<unsigned> monotonicVampireSorts;
  Lib::ZIArray<unsigned> posEqualitiesOnSort;

  SortedSignature* _sig;
  ClauseList* _clauses;
  Lib::DArray<unsigned> _del_f;
  Lib::DArray<unsigned> _del_p;
  Lib::Stack<Lib::DHSet<unsigned>*> _equiv_v_sorts;
  Lib::IntUnionFind _equiv_vs;

  Lib::Stack<std::pair<unsigned,unsigned>>& _sort_constraints;

};

}

#endif // __SortInference__
