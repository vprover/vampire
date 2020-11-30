/**************************************************************************************[VarOrder.h]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef SMTSubsumption_Minisat_VarOrder_h
#define SMTSubsumption_Minisat_VarOrder_h

#include "SMTSubsumption/minisat/SolverTypes.h"
#include "SMTSubsumption/minisat/Heap.h"


namespace SMTSubsumption { namespace Minisat {

//=================================================================================================

// TODO:
//  Select some examples with multiple backtrackings;
//  Check whether decisions make sense
//  (also compare to decisions of old MLMatcher)
//
// Ideas:
// - order by number of alternatives of literal                                         //  these two are "remaining-choices"
// - as tie breaker: try base literals with higher number of variables first            //
// - how to interact with activity?
// Question: how to combine with activity? (alternate in fixed ratio? or multiply values? something else?)
// Try different ways to combine and evaluate:
// - alternate between random/activity (default in minisat)
// - use only remaining-choices heuristic (as described above)
// - alternate between remaining-choices and activity (fixed ratio, try a few different ones; e.g. 0.02, 0.5, 0.8, ....)
// - check paper below, remaining choices divided by activity?
//              intuition: many remaining choices are bad, high activity is good, choose smallest value of (rem. choices / activity)
//              TODO: activity is bumped: 0 -> 1 -> 2 -> 3
//              (rem. choices) / (activity + k)
//              k...constant, the higher k is, the less influence one activity bump has on the heuristic.
//              test different k values: 1, 3, 5, ((10, 100))
//              (considering choice between literals with 2/3 remaining choices: with k=5 e.g. 3 would be preferred over 2 once it has ~3 more activity)
//      => Armin
// (- use rem.choices alone at the beginning of the run, introduce activity later)
//   each decision leads to max. one conflict => activity is useless for small instances
//       => k = 3, 5 probably better, has similar effect and is smoother
// - to compare: record number of decisions !!!
// - priority for test: default minisat heuristic, alternation 0.5, division k=3
//
// - NOTE: this VarOrder selects a boolean variable, but sets of boolean variables represent "integer variables"
//          remaining-choices is defined for "integer variables"
//          So:
//              1. choose the set
//              2. choose boolean variable inside set
//
//          For each set we have two possibilities:
//          a) some undefined, some false, none true
//          b) one true, all others false
//
//          Only a) is possible choice for heuristic.
//          Remaining-choices is the number of undefined variables in the set.
//          We always want to set positive value.
//
//          How to compute activity for the "integer variable"?
//          i) bump "integer variable" whenever corresponding boolean variable is bumped
//                  Q: when analyzing conflict, does each integer variable occur only once?
//                      Not necessarily, e.g., if initial clause is the conflict clause
//                  (if this were true, would be the argument to just bump the integer variable each time the corresponding boolean var is bumped)
//          ii) like i) but implementation in analyze(), and track which "integer variable" has already been bumped (to do it at most once)
// !!       iii) activity of integer variable = max(activity of boolean variable in set)
//                  => keep activity per boolean variable as it is now
//                      (remaining choices still tracked per set)
//              (impl.: one counter per set with bool->set mapping vs. one counter per variable)
//              problem: this must be updated during backtracking; also unnecessary for propagation
//
//
// (technique in newest minisat: no need to check for changes if literal is still true => "blocking literal")
//
//
// TODO: benchmark 'drand' vs. faster custom implementation of choice
//
// TODO: read paper below
// More importantly, we should change VSIDS to take into account the number of
// remaining possibilities for each literal to match to, and prefer those
// literals that are more constrained: CSP-community has already looked at this
// a bit, see e.g.
// https://www.researchgate.net/profile/Christophe_Lecoutre/publication/220838185_Boosting_Systematic_Search_by_Weighting_Constraints/links/55af6bc608aee0799221004e.pdf
//
//
// Statistics:
// - collect #decisions, (#backtrackings; dubious?), success/failure
//   save for each subsumption call, analyze distribution
//   table: (Problem, strategy, Sequence number, #decisions, success/failure)
//          (save premises? because seq number is not enough for LRS/... strategies)
//          => LRS hack: record sequence of limits and replay later (ask Martin Suda if I want to use this)
// - #decisions: both for MLMatcher and SMTSubsumption
// - amount of time spent in FS/BS (e.g., % of overall runtime)
//   second table: (problem, strategy, time FS, time BS, time total)
// - Runs:
//   - with only MLMatcher, collect stats+timings
//   - with only SMTSubsumption, collect stats+timings
//   - (with both, just compare results)
// - strategy:
//   * NOW: default mode with -sa otter -av off -t 60
//   * LATER: portfolio mode
//   * (fishing for good examples: no avatar, otter, no split queues, no additional simplifications)
//
// Then isolate ~100 hardest subsumption instances.


/*

Example:

    Side premise:       P(x)            Q(y)            R(x,y)
                        b1              b2              b3      b4
    Main premise:       P(c)            Q(d)            R(c,c)  R(d,d)

    b1: x->c
    b2: y->d
    b3: x->c,y->c
    b4: x->d,y->d

    What we do:
        ENQUEUE b1
        TPROP ¬b4
        ENQUEUE b2
        TPROP ¬b3
        CONFLICT b3 \/ b4  (when adding the clause)

    If we add the binary clause first, we discover this during propagation of b4:
        PROP b1
        PROP ¬b4 => b3 (CONFLICT with enqueued ¬b3)

    During search, if there's other literals P(e), Q(e):
        DECIDE b1
        TPROP ¬b4
        PROP b3
        TPROP ¬b2
        (ok)
*/





struct VarOrder_lt {
    const vec<double>&  activity;
    bool operator () (Var x, Var y) { return activity[x] > activity[y]; }
    VarOrder_lt(const vec<double>&  act) : activity(act) { }
};

class VarOrder {
    const vec<char>&    assigns;     // var->val. Pointer to external assignment table.
    const vec<double>&  activity;    // var->act. Pointer to external activity table.
    Heap<VarOrder_lt>   heap;
    double              random_seed; // For the internal random number generator

public:
    VarOrder(const vec<char>& ass, const vec<double>& act) :
        assigns(ass), activity(act), heap(VarOrder_lt(act)), random_seed(91648253)
        { }

    inline void newVar(void);
    inline void update(Var x);                  // Called when variable increased in activity.
    inline void undo(Var x);                    // Called when variable is unassigned and may be selected again.
    inline Var  select(double random_freq =.0); // Selects a new, unassigned variable (or 'var_Undef' if none exists).
};


void VarOrder::newVar(void)
{
    heap.setBounds(assigns.size());
    heap.insert(assigns.size()-1);
}


void VarOrder::update(Var x)
{
    if (heap.inHeap(x))
        heap.increase(x);
}


void VarOrder::undo(Var x)
{
    if (!heap.inHeap(x))
        heap.insert(x);
}


Var VarOrder::select(double random_var_freq)
{
    // TODO: plugin our heuristic (instead of random)
    // Random decision:
    if (drand(random_seed) < random_var_freq && !heap.empty()){
        Var next = irand(random_seed,assigns.size());
        if (toLbool(assigns[next]) == l_Undef)
            return next;
    }

    // Activity based decision:
    while (!heap.empty()){
        Var next = heap.getmin();
        if (toLbool(assigns[next]) == l_Undef)
            return next;
    }

    return var_Undef;
}


} }

//=================================================================================================
#endif
