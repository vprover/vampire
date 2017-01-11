/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#ifndef __InterpolantsNew__
#define __InterpolantsNew__

#include <stack>
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
         * computes interpolant for a given local proof
         */
        Kernel::Formula* getInterpolant(Kernel::Unit* refutation);
        
        /*
         * helper method:
         * implements so called "splitting function" from the thesis.
         * Currently approach 1 from section 3.3 of the thesis is implemented
         */
        void computeSplittingFunction(Kernel::Unit* conclusion);
        
    private:
        
        /*
         * helper methods
         */
        typedef std::unordered_map<Kernel::Unit*, std::unordered_set<Kernel::Unit*>> BoundaryMap;
        std::unordered_map<Kernel::Unit*, Kernel::Unit*> computeSubproofs(Kernel::Unit* refutation);
        std::pair<BoundaryMap, BoundaryMap> computeBoundaries(std::unordered_map<Kernel::Unit*, Kernel::Unit*> unitsToRepresentative, Kernel::Unit* refutation);
        Kernel::Formula* generateInterpolant(std::pair<BoundaryMap, BoundaryMap> boundaries);
        
        /*
         * methods used to implement union find: root, find and merge (aka union)
         */
        typedef std::unordered_map<Kernel::Unit*, Kernel::Unit*> UnionFindMap;
        Kernel::Unit* root(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit);
        bool find(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit1, Kernel::Unit* unit2);
        void merge(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit1, Kernel::Unit* unit2);

    };
};
#endif // __InterpolantsNew__