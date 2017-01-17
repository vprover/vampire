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
    /*
     * main class for deriving craig-interpolants
     * computes interpolants from local refutations
     * algorithms are based on master thesis of Bernhard Gleiss
     */
    class InterpolantsNew
    {
    public:
        InterpolantsNew(){}
        
        /*
         * controls which quality measurement is used for creating the interpolant
         */
        enum UnitWeight
        {
            VAMPIRE, // the weight usually used in vampire, i.e. number of symbols
            QUANTIFIED_VARS // use number of different quantified vars as weight
        };
        
        /*
         * main method to call
         * computes interpolant for a given local proof.
         * implements interpolation algorithm stated on page 13 of the thesis
         *
         * internally calls computeSplittingFunction to
         * determine how to split the proof
         * @pre: refutation must be a local refutation
         */
        Kernel::Formula* getInterpolant(Kernel::Unit* refutation, UnitWeight weightFunction);
        
    protected:
        /*
         * implements so called "splitting function" from the thesis
         * (uses improved version of approach #2, cf. section 3.3).
         */
        virtual void computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction);
        
        /*
         * helper method to compute the weight of a unit
         */
        double weightForUnit(Kernel::Unit* unit, UnitWeight weightFunction);
        
    private:
        /*
         * preprocesses proofs by removing all inferences
         * which are derived only from theory axioms
         * called by getInterpolant
         * @pre:  all input inferences of refutation have their inheritedColor assigned to
         * either COLOR_LEFT, COLOR_RIGHT or COLOR_TRANSPARENT
         * @post: all input inferences of refutation have their inheritedColor assigned to
         * either COLOR_LEFT or COLOR_RIGHT
         */
        void removeTheoryInferences(Kernel::Unit* refutation);
        
        /*
         * helper methods to compute interpolant
         */
        typedef std::unordered_map<Kernel::Unit*, std::unordered_set<Kernel::Unit*>> BoundaryMap;
        std::unordered_map<Kernel::Unit*, Kernel::Unit*> computeSubproofs(Kernel::Unit* refutation);
        std::pair<const BoundaryMap, const BoundaryMap> computeBoundaries(const std::unordered_map<Kernel::Unit*, Kernel::Unit*>& unitsToRepresentative, Kernel::Unit* refutation);
        Kernel::Formula* generateInterpolant(std::pair<const BoundaryMap, const BoundaryMap>& boundaries);
        

        
        /*
         * methods used to implement union find: root, find and merge (aka union)
         */
        typedef std::unordered_map<Kernel::Unit*, Kernel::Unit*> UnionFindMap;
        Kernel::Unit* root(const UnionFindMap& unitsToRepresentative, Kernel::Unit* unit);
        bool find(UnionFindMap& unitsToRepresentative, Kernel::Unit* unit1, Kernel::Unit* unit2);
        void merge(UnionFindMap& unitsToRepresentative, std::unordered_map<Kernel::Unit*, int> unitsToSize, Kernel::Unit* unit1, Kernel::Unit* unit2);

    };
};
#endif // __InterpolantsNew__