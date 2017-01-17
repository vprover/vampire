/**
 * @file InterpolantMinimizerNew.hpp
 * Implements class InterpolantMinimizerNew.
 * @author Bernhard Gleiss
 */

#ifndef __InterpolantMinimizerNew__
#define __InterpolantMinimizerNew__

#include "InterpolantsNew.hpp"
#include <stack>

//#if VZ3
namespace Shell
{
    /*
     * subclass of InterpolantsNew, which overrides
     * splitting function to use optimized approach
     * described in the thesis
     */
    class InterpolantMinimizerNew : public InterpolantsNew
    {
    public:
        InterpolantMinimizerNew(){}
        /*
         * implements so called "splitting function" from the thesis.
         * uses approach #3 (cf. section 3.3 and algorithm 3): 
         * encode optimal splitting function as optimization problem 
         * and ask solver for an optimal solution
         * we use z3 as solver
         */
        virtual void computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction) override;
    };
};
//#endif // VZ3

#endif // __InterpolantMinimizerNew__