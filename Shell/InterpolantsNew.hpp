/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#ifndef __InterpolantsNew__
#define __InterpolantsNew__

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
         * preprocesses proofs by removing all inferences
         * which are derived only from theory axioms,
         * since we don't need those for interpolation,
         * but sometimes the existence of those inferences yields a bigger interpolant.
         *
         * usually called before call to getInterpolant
         *
         * @pre:  all input inferences of refutation have their inheritedColor assigned to
         * either COLOR_LEFT, COLOR_RIGHT or COLOR_TRANSPARENT
         * @post: all input inferences of refutation have their inheritedColor assigned to
         * either COLOR_LEFT or COLOR_RIGHT
         */
        void removeTheoryInferences(Kernel::Unit* refutation);
        
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
        virtual std::unordered_map<Kernel::Unit*, Kernel::Color> computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction);
        
        /*
         * helper method to compute the weight of a unit
         */
        double weightForUnit(Kernel::Unit* unit, UnitWeight weightFunction);
        
        // TODO: make the following three methods private again after benchmarking
        /*
         * helper methods to compute interpolant
         */
        typedef std::unordered_map<Kernel::Unit*, std::unordered_set<Kernel::Unit*>> BoundaryMap;
        std::unordered_map<Kernel::Unit*, Kernel::Unit*> computeSubproofs(Kernel::Unit* refutation,
                                                                          const std::unordered_map<Kernel::Unit*,Kernel::Color> splittingFunction);
        std::pair<const BoundaryMap, const BoundaryMap> computeBoundaries(Kernel::Unit* refutation,
                                                                          const std::unordered_map<Kernel::Unit*, Kernel::Color> splittingFunction,
                                                                          const std::unordered_map<Kernel::Unit*, Kernel::Unit*>& unitsToRepresentative);
        Kernel::Formula* generateInterpolant(std::pair<const BoundaryMap, const BoundaryMap>& boundaries);
    private:
      
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
