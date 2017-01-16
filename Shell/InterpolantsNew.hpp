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
         * computes interpolant for a given local proof.
         * implements interpolation algorithm stated on page 13 of master thesis of Bernhard Gleiss
         *
         * internally calls computeSplittingFunction to
         * determine how to split the proof
         */
        Kernel::Formula* getInterpolant(Kernel::Unit* refutation);
        
    protected:
        /*
         * implements so called "splitting function" from the thesis
         * (uses improved version of approach #2, cf. section 3.3).
         */
        virtual void computeSplittingFunction(Kernel::Unit* refutation);
        
    private:
        
        /*
         * helper methods
         */
        typedef std::unordered_map<Kernel::Unit*, std::unordered_set<Kernel::Unit*>> BoundaryMap;
        std::unordered_map<Kernel::Unit*, Kernel::Unit*> computeSubproofs(Kernel::Unit* refutation);
        std::pair<const BoundaryMap, const BoundaryMap> computeBoundaries(std::unordered_map<Kernel::Unit*, Kernel::Unit*>& unitsToRepresentative, Kernel::Unit* refutation);
        Kernel::Formula* generateInterpolant(std::pair<const BoundaryMap, const BoundaryMap>& boundaries);
        
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