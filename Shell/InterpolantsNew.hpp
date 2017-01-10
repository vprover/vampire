/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#ifndef __InterpolantsNew__
#define __InterpolantsNew__

#include <queue>
#include <unordered_set>
#include <unordered_map>
#include "Forwards.hpp"

namespace Shell
{
    class InterpolantsNew
    {
    public:
        InterpolantsNew(){}
        
        /*
         * main method to call
         * implements interpolation algorithm stated on page 13 of
         * master thesis of Bernhard Gleiss
         */
        Kernel::Formula* getInterpolant(Kernel::Unit* refutation);
        
    private:
        /*
         * implements so called "splitting function" from the thesis.
         * Currently approach 1 from section 3.3 of the thesis is implemented
         */
        bool inferenceIsColoredRed(Kernel::Unit* conclusion);
        
        /*
         * methods used to implement union find: root, find and merge (aka union)
         * https://www.cs.princeton.edu/~rs/AlgsDS07/01UnionFind.pdf
         */
        typedef std::unordered_map<Kernel::Unit*, Kernel::Unit*> UnionFindMap;
        Kernel::Unit* root(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit);
        bool find(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit1, Kernel::Unit* unit2);
        void merge(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit1, Kernel::Unit* unit2);

    };
};
#endif // __InterpolantsNew__