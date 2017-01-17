/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#include "InterpolantsNew.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Debug/Assertion.hpp"
#include <assert.h>

/*
 * note that formulas are implemented as both formulas (usual formulas) and 
 * clauses (vectors of literals) for efficiency. If we don't care about the
 * difference (as in this class), we use the class Unit, which wraps around
 * formulas and clauses, abstracting away the differences.
 * ========================================================================
 * We conceptually think of proofs as DAGS, where the nodes are inferences:
 * Each such inference i has some premises (n_i=#premises, n_i>=0), a conclusion
 * and n_i parent inferences.
 *
 * Due to performance reasons, a proof nonetheless consists not of inferences,
 * but of the conclusions of those inferences (and these
 * conclusions are not formulas but more generally units).
 * Each such conclusion c (conceptually of an inference inf_c) points to the 
 * conclusions of each parent inference of inf_c.
 * ========================================================================
 * Additionally to the proof-information, we use coloring information,
 * which is created during parsing:
 * 1) For each symbol, we can use getColor() to query if that symbol is A-local,
 *    B-local or global (COLOR_LEFT, COLOR_RIGHT or COLOR_TRANSPARENT).
 *    getColor() is also extended in the obvious way to formulas and clauses.
 * 2) For each input formula, we can use inheritedColor() to query if that
 *    formula is part of the A-formula, part of the B-formula or part of the
 *    theory axioms (COLOR_LEFT, COLOR_RIGHT or COLOR_TRANSPARENT)
 * We use both of them in the method computeSplittingFunction(), which reuses
 * the inheritedColor-field to save its result.
 * ========================================================================
 * Note that the word 'splitting' is used with two different meanings in
 * this class: 1) splitting a proof into an A- and a B- part as described
 *                in the thesis
 *             2) splitting the proof for Avatar
 */

namespace Shell
{
    using namespace Kernel;
    
    
#pragma mark - preprocessing proof
    
    void InterpolantsNew::removeTheoryInferences(Unit* refutation)
    {
        // traverse the proof in depth-first post order
        ProofIteratorPostOrder it(refutation);
        while (it.hasNext())
        {
            Unit* current = it.next();
            assert((!InferenceStore::instance()->getParents(current).hasNext() &&  (   current->inheritedColor() == COLOR_LEFT
                                                                                        || current->inheritedColor() == COLOR_RIGHT
                                                                                        || current->inheritedColor() == COLOR_TRANSPARENT
                                                                                        ))
                   || (InferenceStore::instance()->getParents(current).hasNext() &&  current->inheritedColor() == COLOR_INVALID));

            
            bool hasGreyParents = false;
            bool hasNonGreyParents = false;
            
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
            while (parents.hasNext())
            {
                Unit* premise = parents.next();
                if (premise->inheritedColor() == COLOR_TRANSPARENT)
                {
                    hasGreyParents = true;
                }
                else
                {
                    hasNonGreyParents = true;
                }
            }
            
            // whenever a non-input-inference has only grey parents, color it grey too (needed to compute which inferences are derived only from theory axioms)
            if (current->inheritedColor() == COLOR_INVALID && !hasNonGreyParents)
            {
                current->setInheritedColor(COLOR_TRANSPARENT);
            }
            
            // whenever an inference has both grey parents and non-grey parents, remove the grey parents
            if (hasGreyParents && hasNonGreyParents)
            {
                UnitList* premises = UnitList::empty();

                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    if (premise->inheritedColor() != COLOR_TRANSPARENT)
                    {
                        UnitList::push(premise, premises);
                    }
                    else
                    {
                        premise->decRefCnt();
                    }
                }
                
                Inference* inference = new InferenceMany(current->inference()->rule(), premises);
                current->setInference(inference);
            }
        }
    }
    
    
#pragma mark - main method

    /*
     * main method
     * cf. Definition 3.1.2 of the thesis
     */
    Formula* InterpolantsNew::getInterpolant(Unit *refutation, UnitWeight weightFunction)
    {

        /*
         * start by removing theory inferences, since we don't need those for interpolation,
         * but sometimes the existence of those inferences yields a bigger interpolant
         */
        removeTheoryInferences(refutation);
        
        /*
         * compute coloring for the inferences, i.e. compute splitting function in the words of the thesis
         * Note: reuses inheritedColor-field to save result
         */
        computeSplittingFunction(refutation, weightFunction);
        
        /*
         * compute A-subproofs
         */
        const std::unordered_map<Unit*, Unit*> unitsToRepresentative = computeSubproofs(refutation);
        
        /*
         * collect all boundaries of the subproofs
         */
        auto boundaries = computeBoundaries(unitsToRepresentative, refutation);
        
        /*
         * generate the interpolant (i.e. the splitting formula in the words of the thesis, cf. Definition 3.1.2. of the thesis)
         */
        const auto interpolant = generateInterpolant(boundaries);
        
        return interpolant;
    }
    
    
#pragma mark - main helper methods
    
    /*
     * compute the maximal A-subproofs of the proofs using standard union-find ideas as described in the thesis
     * Note: can't just use depth-first-search, since edge information is only saved in one direction in the nodes
     * Note: We represent each subproof by the conclusion of one of its inferences (the so called representative unit)
     */
    std::unordered_map<Unit*, Unit*> InterpolantsNew::computeSubproofs(Unit* refutation)
    {
        std::unordered_map<Unit*, Unit*> unitsToRepresentative; // maps each unit u1 (belonging to a red subproof) to the representative unit u2 of that subproof
        std::unordered_map<Unit*, int> unitsToSize; // needed for weighted quick-union: for each unit, counts number of elements rooted in that unit
        
        std::unordered_set<Unit*> processed; // keep track of already visited units.
        std::queue<Unit*> queue; // used for BFS
        queue.push(refutation);
        
        // iterative Breadth-first search (BFS) through the proof DAG
        while (!queue.empty())
        {
            Unit* currentUnit = queue.front();
            queue.pop();
            processed.insert(currentUnit);
            
            // add unprocessed premises to queue for BFS:
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
            
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                // if we haven't processed the current premise yet
                if (processed.find(premise) == processed.end())
                {
                    // add it to the queue
                    queue.push(premise);
                }
            }
            
            // standard union-find: if current inference is assigned to A-part of the proof,
            if (currentUnit->inheritedColor() == COLOR_LEFT)
            {
                parents = InferenceStore::instance()->getParents(currentUnit);
                // then for each parent inference,
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // if it is assigned to the A-part of the proof
                    if (premise->inheritedColor() == COLOR_LEFT)
                    {
                        // merge the subproof of the current inference with the subproof of the parent inference
                        merge(unitsToRepresentative, unitsToSize, currentUnit, premise);
                    }
                }
            }
        }

        return unitsToRepresentative;
    }
    
    
    /*
     * computes the boundaries of the A-subproofs using Breadth-first search (BFS)
     * Using idea from the thesis: a unit occurs as boundary of a subproof, if it has a different color than of its parents/ one of its children.
     */
    std::pair<const InterpolantsNew::BoundaryMap, const InterpolantsNew::BoundaryMap> InterpolantsNew::computeBoundaries(const std::unordered_map<Unit*, Unit*>& unitsToRepresentative, Unit* refutation)
    {
        // Note: unordered_map never copies its values during rehashing, so no unique pointers are needed here!
        std::unordered_map<Unit*, std::unordered_set<Unit*>> unitsToTopBoundaries; // maps each representative unit of a subproof to the top boundaries of that subproof
        std::unordered_map<Unit*, std::unordered_set<Unit*>> unitsToBottomBoundaries; // maps each representative unit of a subproof to the bottom boundaries of that subproof
        
        std::unordered_set<Unit*> processed; // keep track of already visited units.
        std::queue<Unit*> queue; // used for BFS
        queue.push(refutation);
        
        // iterative BFS through the proof DAG
        while (!queue.empty())
        {
            Unit* currentUnit = queue.front();
            queue.pop();
            processed.insert(currentUnit);
            
            // add unprocessed premises to queue for BFS:
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
            
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                // if we haven't processed the current premise yet
                if (processed.find(premise) == processed.end())
                {
                    // add it to the queue
                    queue.push(premise);
                }
            }
            
            // if current inference is assigned to A-part
            assert(currentUnit->inheritedColor() == COLOR_LEFT || currentUnit->inheritedColor() == COLOR_RIGHT);
            if (currentUnit->inheritedColor() == COLOR_LEFT)
            {
                Unit* rootOfCurrent = root(unitsToRepresentative, currentUnit);
                parents = InferenceStore::instance()->getParents(currentUnit);
                
                // then for each parent inference,
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();

                    // if it is assigned to the B-part
                    assert(premise->inheritedColor() == COLOR_LEFT || premise->inheritedColor() == COLOR_RIGHT);
                    if (premise->inheritedColor() != COLOR_LEFT)
                    {
                        // add the premise (i.e. the conclusion of the parent inference) to upper boundaries of the subproof of currentUnit:
                        unitsToTopBoundaries[rootOfCurrent].insert(premise);
                    }
                }
            }
            
            // if current inference is assigned to B-part
            else
            {
                parents = InferenceStore::instance()->getParents(currentUnit);
                
                // then for each parent inference,
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // if it is assigned to the A-part
                    assert(premise->inheritedColor() == COLOR_LEFT || premise->inheritedColor() == COLOR_RIGHT);
                    if (premise->inheritedColor() == COLOR_LEFT)
                    {
                        Unit* rootOfPremise = root(unitsToRepresentative, premise);
                        
                        // add the premise (i.e. the conclusion of the parent inference) to upper boundaries of the subproof of currentUnit:
                        unitsToBottomBoundaries[rootOfPremise].insert(premise);
                    }
                }
            }
        }
        
        // we finally have to check for the empty clause, if it appears as boundary of an A-subproof
        if (refutation->inheritedColor() == COLOR_LEFT)
        {
            assert(root(unitsToRepresentative, refutation) == refutation);
            unitsToBottomBoundaries[refutation].insert(refutation);
        }

        return make_pair(std::move(unitsToTopBoundaries), std::move(unitsToBottomBoundaries));
    }
    
    /*
     * generate the interpolant from the boundaries as described in the thesis
     * Note: we already have collected all relevant information before calling this function, 
     * we now just need to build (and simplify) a formula out of the information.
     */
    Formula* InterpolantsNew::generateInterpolant(std::pair<const InterpolantsNew::BoundaryMap, const InterpolantsNew::BoundaryMap>& boundaries)
    {
        const std::unordered_map<Unit*, std::unordered_set<Unit*>>& unitsToTopBoundaries = boundaries.first;
        const std::unordered_map<Unit*, std::unordered_set<Unit*>>& unitsToBottomBoundaries = boundaries.second;
        
        FormulaList* outerConjunction = FormulaList::empty();
        
        // Note: there are potentially subproofs without either topBoundaries or lowerBoundaries, so we
        // compute list of all subproof representatives by conjoining keys of unitsToTopRepresentatives and
        // unitsToBottomRepresentatives
        std::unordered_set<Unit*> roots;
        for (const auto& keyValuePair : unitsToTopBoundaries)
        {
            roots.insert(keyValuePair.first);
        }
        for(const auto& keyValuePair : unitsToBottomBoundaries)
        {
            roots.insert(keyValuePair.first);
        }
        
        // for each subproof
        for (const auto& root : roots)
        {
            // generate conjunction of topBoundaries
            FormulaList* conjunction1List = FormulaList::empty();

            auto it1 = unitsToTopBoundaries.find(root);
            if (it1 != unitsToTopBoundaries.end())
            {
                const std::unordered_set<Unit*>& topBoundaries = (*it1).second;
                
                for (const auto& boundary : topBoundaries)
                {
                    FormulaList::push(boundary->getFormula(), conjunction1List);
                }
            }
            Formula* conjunction1 = JunctionFormula::generalJunction(Connective::AND, conjunction1List);

            // generate conjunction of bottomBoundaries
            FormulaList* conjunction2List = FormulaList::empty();
            
            auto it2 = unitsToBottomBoundaries.find(root);
            if (it2 != unitsToBottomBoundaries.end())
            {
                const std::unordered_set<Unit*>& bottomBoundaries = (*it2).second;
                
                for (const auto& boundary : bottomBoundaries)
                {
                    FormulaList::push(boundary->getFormula(), conjunction2List);
                }
            }
            Formula* conjunction2 = JunctionFormula::generalJunction(Connective::AND, conjunction2List);
            
            // generate implication "(conj. of topBoundaries) implies (conj. of bottomBoundaries)"
            // NOTE: we perform simplifications of C->D:
            Formula* implication;
            if (conjunction2->connective() == Connective::TRUE)// C->Top => Top
            {
                implication = conjunction2;
            }
            else if (conjunction1->connective() == Connective::TRUE)// Top->D => D
            {
                implication = conjunction2;
            }
            else if (conjunction1->connective() == Connective::FALSE)// Bot->D => Top
            {
                implication = new NegatedFormula(conjunction1);
            }
            else if (conjunction2->connective() == Connective::FALSE)// C->Bot => neg(C)
            {
                implication = new NegatedFormula(conjunction1);
            }
            else // no simplification, construct C->D
            {
                FormulaList* implicationList = FormulaList::empty();
                FormulaList::push(new NegatedFormula(conjunction1), implicationList);
                FormulaList::push(conjunction2, implicationList);
                
                implication = JunctionFormula::generalJunction(Connective::OR, implicationList);
            }
            
            // simplify the arguments for outer conjunction
            if (implication->connective() != Connective::TRUE) // skip argument, since it is redundant
            {
                if (implication->connective() == Connective::FALSE) // if one of the arguments is bottom, the outerConjunction will be bottom, so clear arguments and stop adding new ones
                {
                    outerConjunction = FormulaList::empty();
                    FormulaList::push(implication, outerConjunction);
                    break;
                }
                else // no simplification
                {
                    // add implication to outerConjunction
                    FormulaList::push(implication, outerConjunction);
                }
            }
        }
        
        // finally conjoin all generated implications and return the result, which is the interpolant
        Formula* interpolant = JunctionFormula::generalJunction(Connective::AND, outerConjunction);
        
        return interpolant;
    }


    #pragma mark - splitting function
 
    /*
     * implements local splitting function from the thesis (improved version of approach #2, cf. section 3.3)
     */
    void InterpolantsNew::computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction)
    {
        std::stack<Unit*> stack; // used for DFS
        stack.push(refutation);
        
        // iterative post-order depth-first search (DFS) through the proof DAG
        // following the usual ideas, e.g.
        // https://pythonme.wordpress.com/2013/08/05/algorithm-iterative-dfs-depth-first-search-with-postorder-and-preorder/
        // Note: we keep track of visited nodes using the inheritedColor-field,
        // which is COLOR_LEFT or COLOR_RIGHT iff the inference was already visited
        // or is an axiom and therefore doesn't need to be visited
        while (!stack.empty())
        {
            Unit* currentUnit = stack.top();
            
            assert((!InferenceStore::instance()->getParents(currentUnit).hasNext() && (currentUnit->inheritedColor() == COLOR_LEFT || currentUnit->inheritedColor() == COLOR_RIGHT)) || (InferenceStore::instance()->getParents(currentUnit).hasNext() &&  currentUnit->inheritedColor() == COLOR_INVALID));

            bool existsUnvisitedParent = false;
            // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
            // for currentUnit now, but wait until those unprocessed premises are processed.
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
            
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                // if we haven't processed the current premise yet
                if (premise->inheritedColor() == COLOR_INVALID)
                {
                    // add it to the stack
                    stack.push(premise);
                    existsUnvisitedParent = true;
                }
            }

            // if we already colored all parent-inferences, we can color the inference too
            if (!existsUnvisitedParent)
            {
                // we only assign non-axioms, since axioms are already assigned accordingly
                // (the requirement of a splitting function (in the words of the thesis) is therefore
                // fulfilled)
                assert(currentUnit->inheritedColor() == COLOR_INVALID);

                // if the inference contains a colored symbol, assign it to the corresponding partition (this
                // ensures requirement of a LOCAL splitting function in the words of the thesis):
                // - this is the case if either the conclusion contains a colored symbol
                if (currentUnit->getColor() == COLOR_LEFT || currentUnit->getColor() == COLOR_RIGHT)
                {
                    //cout << "coloring " << currentUnit->toString() << (currentUnit->getColor() == COLOR_LEFT ? " red" : " blue") << endl;
                    currentUnit->setInheritedColor(currentUnit->getColor());
                    
                    goto END;
                }
                
                // - or if any premise contains a colored symbol
                { // scoping necessary due to goto
                    VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
                    while (parents.hasNext())
                    {
                        Unit* premise= parents.next();
                        
                        if (premise->getColor() == COLOR_LEFT || premise->getColor() == COLOR_RIGHT)
                        {
                            //cout << "coloring " << currentUnit->toString() << (premise->getColor() == COLOR_LEFT ? " red" : " blue") << endl;
                            currentUnit->setInheritedColor(premise->getColor());
                            
                            goto END;
                        }
                    }
                }
                
                /* otherwise we choose the following heuristic
                 * if the weighted sum of the conclusions of all parent inferences assigned
                 * to the red partition is greater than the weighted sum of the conclusions
                 * of all parent inferences assigned to the blue partition, then
                 * assign the inference to red, otherwise to blue
                 */
                { // scoping necessary due to goto
                    parents = InferenceStore::instance()->getParents(currentUnit);
                    
                    double difference = 0;
                    while (parents.hasNext())
                    {
                        Unit* premise= parents.next();
                        
                        assert(premise->inheritedColor() == COLOR_LEFT || premise->inheritedColor() == COLOR_RIGHT);
                        if (premise->inheritedColor() == COLOR_LEFT)
                        {
                            difference += weightForUnit(premise, weightFunction);
                        }
                        else
                        {
                            difference -= weightForUnit(premise, weightFunction);
                        }
                    }
                    //cout << "coloring " << currentUnit->toString() << (difference > 0 ? " red" : " blue") << endl;
                    currentUnit->setInheritedColor(difference > 0 ? COLOR_LEFT : COLOR_RIGHT);
                }
                
                // we are now finished with currentUnit, so pop it
            END:
                stack.pop();
            }
        }
    }
    
#pragma mark - helper method for unit weight
    
    double InterpolantsNew::weightForUnit(Kernel::Unit* unit, UnitWeight weightFunction)
    {
        return 1;
//        if (weightFunction == UnitWeight::VAMPIRE)
//        {
//            // TODO: proper weight here!
//        }
//        else
//        {
//            assert(weightFunction == UnitWeight::QUANTIFIED_VARS);
//            return unit->varCnt();
//        }
    }


#pragma mark - union find helper methods
    
  /*
   * standard implementation of union-find following
   * https://www.cs.princeton.edu/~rs/AlgsDS07/01UnionFind.pdf
   * Note: we keep the invariant that we omit from the map the units which map to themselves
   * Note: we don't apply path compression. That would possibly be a little 
   * bit faster, but then we couldn't make the unitsToRepresentative-argument 
   * of the root-function const.
   */
    
    Kernel::Unit* InterpolantsNew::root(const UnionFindMap& unitsToRepresentative, Unit* unit)
    {
        Unit* root = unit;
        while (unitsToRepresentative.find(root) != unitsToRepresentative.end())
        {
            assert(unitsToRepresentative.at(root) != root);
            root = unitsToRepresentative.at(root);
        }
        
        return root;
    }
    
    bool InterpolantsNew::find(UnionFindMap& unitsToRepresentative, Unit* unit1, Unit* unit2)
    {
        return root(unitsToRepresentative, unit1) == root(unitsToRepresentative, unit2);
    }
    
    void InterpolantsNew::merge(UnionFindMap& unitsToRepresentative,
                                std::unordered_map<Unit*, int> unitsToSize,
                                Unit* unit1,
                                Unit* unit2)
    {
        assert(unit1 != unit2);
        Unit* root1 = root(unitsToRepresentative, unit1);
        Unit* root2 = root(unitsToRepresentative, unit2);
        
        if (root1 != root2)
        {
            if (unitsToSize[root1] < unitsToSize[root2]) // weighted version
            {
                unitsToRepresentative[root1] = root2;
                unitsToSize[root2] += unitsToSize[root1];
            }
            else
            {
                unitsToRepresentative[root2] = root1;
                unitsToSize[root1] += unitsToSize[root2];
            }
        }
    }
}