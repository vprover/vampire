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
 * @file Interpolants.cpp
 * Implements class Interpolants.
 * @author Bernhard Gleiss
 */

#ifndef __Interpolants__
#define __Interpolants__

#include <unordered_set>
#include <unordered_map>
#include <stack>
#include <queue>

#include "Forwards.hpp"

namespace Shell
{
    /*
    * iterator, which traverses the proof in depth-first post-order.
    */
    class ProofIteratorPostOrder
    {
    public:
      ProofIteratorPostOrder(Kernel::Unit* refutation);
      bool hasNext();
      Kernel::Unit* next();

    private:
      std::stack<Kernel::Unit*> todo;
      std::unordered_set<Kernel::Unit*> visited; // the units we have already visited
    };

    /*
    * iterator, which traverses the proof in breadth-first pre-order.
    */
    class ProofIteratorBFSPreOrder
    {
    public:
      ProofIteratorBFSPreOrder(Kernel::Unit* refutation);
      bool hasNext();
      Kernel::Unit* next();

    private:
      std::queue<Kernel::Unit*> todo;
      std::unordered_set<Kernel::Unit*> visited; // the units we have already visited
    };


    /*
     * main class for deriving craig-interpolants
     * computes interpolants from local refutations
     * algorithms are based on master thesis of Bernhard Gleiss
     */
    class Interpolants
    {
    public:
        Interpolants(){}
        
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

        // method moved from "old" Interpolants implementation
        /**
         * Any pre-processing of the refutation before interpolation is considered.
         *
         * We remove the leafs corresponding to the conjecture
         * and leave the negated_conjecture child of this unit as the leaf instead.
         * (Inference::NEGATED_CONJECTURE is not sound).
         */
        static void removeConjectureNodesFromRefutation(Kernel::Unit* refutation);

        // method moved from "old" Interpolants implementation
        /**
         * Turn all Units in a refutation into FormulaUnits (casting Clauses to Formulas and wrapping these as Units).
         *
         * Keep the old refutation (= non-destructive). Possible sharing of the formula part of the original refutation.
         *
         * Assume that once we have formula on a parent path we can't go back to a clause.
         *
         */
        static Kernel::Unit* formulifyRefutation(Kernel::Unit* refutation);
    protected:
        
        /*
         * implements so called "splitting function" from the thesis
         * (uses improved version of approach #2, cf. section 3.3).
         */
        typedef std::unordered_map<Kernel::Unit*, Kernel::Color> SplittingFunction;
        virtual SplittingFunction computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction);
        
        /*
         * helper method to compute the weight of a unit
         */
        double weightForUnit(Kernel::Unit* unit, UnitWeight weightFunction);
        
        // TODO: make the following three methods private again after benchmarking
        /*
         * helper methods to compute interpolant
         */
        typedef std::unordered_map<Kernel::Unit*, Kernel::Unit*> SubproofsUnionFind;
        SubproofsUnionFind computeSubproofs(Kernel::Unit* refutation, const SplittingFunction& splittingFunction);

        typedef std::pair<const std::unordered_set<Kernel::Unit*>, const std::unordered_set<Kernel::Unit*>> Boundary; // pair of inputNodes and outputNodes
        Boundary computeBoundary(Kernel::Unit* refutation, const SplittingFunction& splittingFunction);
        Kernel::Formula* generateInterpolant(Kernel::Unit* refutation, const Boundary& boundary, const SplittingFunction& splittingFunction,
                                                                 const SubproofsUnionFind& unitsToRepresentative);
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
#endif // __Interpolants__
