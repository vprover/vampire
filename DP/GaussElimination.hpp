/*
 * File GaussElimination.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file GaussElimination.hpp
 */

#ifndef __GaussElimination__
#define __GaussElimination__

//#include "Forwards.hpp"

namespace DP
{
    //using namespace Lib;
    //using namespace Kernel;

    class GaussElimination
    {
    public:
        //CLASS_NAME(GaussElimination);
        //USE_ALLOCATOR(GaussElimination);

        GaussElimination(float **augmentedMatrix, int numberOfUnkowns, int numberOfEquations);

        void solve();

    private:
        float **augmentedMatrix;
        int numberOfUnkowns;
        int numberOfEquations;
    };

}

#endif // __GaussElimination__
