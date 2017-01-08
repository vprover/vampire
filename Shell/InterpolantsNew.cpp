/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#include <Kernel/Formula.hpp>
#include "Kernel/Connective.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "InterpolantsNew.hpp"

#include <assert.h> //TODO: how to do assertions in vampire?
namespace Shell
{
    using namespace Kernel;
 
#pragma mark - main methods
    /*
     * note that a proof in vampire consists not of inferences,
     * but of the antecedents of those inferences (and these
     * antecendents are not formulas but more generally units).
     */
    Formula* InterpolantsNew::getInterpolant(Unit *refutation)
    {
        /*
         * Part 1: 
         * compute A-subproofs
         */
    
        std::unordered_map<Unit*, Unit*> unitsToRepresentative; // maps each unit u1 (belonging to a red subproof) to the representative unit u2 of that subproof
        
        std::unordered_set<Unit*> processed; // keep track of already visited units.
        std::queue<Unit*> queue; // used for BFS
        queue.push(refutation);
    
        // iterative Breadth-first search (BFS) through the proof DAG
        while (!queue.empty())
        {
            Unit* currentUnit = queue.front();
            queue.pop();
            cout << "current unit: " << currentUnit->toString() << endl;

            // add unprocessed premises to queue for BFS:
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
            
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                // if we haven't processed the current premise yet
                // TODO: remove hack
                if (processed.find(premise) == processed.end() && premise->inference()->rule() != Inference::INPUT)
                {
                    // add it to the queue
                    queue.push(premise);
                }
            }
            
            // if current inference is assigned to A-part of the proof,
            if (inferenceIsColoredRed(currentUnit))
            {
                parents = InferenceStore::instance()->getParents(currentUnit);
                // then for each parent inference,
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // if it is assigned to the A-part of the proof
                    // TODO: remove hack
                    if (inferenceIsColoredRed(premise) && premise->inference()->rule() != Inference::INPUT)
                    {
                        // merge the subproof of the current inference with the subproof of the parent inference
                        merge(unitsToRepresentative, currentUnit, premise);
                    }
                }
            }
        }
        
        cout << endl << "unitsToRepresentative map:\n";
        for (const auto& keyValuePair : unitsToRepresentative)
        {
            cout << "(" << keyValuePair.first->toString() << ", " << keyValuePair.second->toString() << ")" << endl;

        }
        cout << endl;

        
        /* 
         * Part 2:
         * collect all boundaries of the subproofs
         */
        
        // TODO: replace std::vector with a hash-set taking pointer-adresses for hash-computation (i.e. pointers with the same address must yield the same hash )
        std::unordered_map<Unit*, std::vector<Unit*>> unitsToTopBoundaries; // maps each representative unit of a subproof to the top boundaries of that subproof
        std::unordered_map<Unit*, std::vector<Unit*>> unitsToBottomBoundaries; // maps each representative unit of a subproof to the bottom boundaries of that subproof
        
        processed.clear();
        ASSERT(queue.empty());
        queue.push(refutation);

        // iterative Breadth-first search (BFS) through the proof DAG
        while (!queue.empty())
        {
            Unit* currentUnit = queue.front();
            queue.pop();
            cout << "current unit: " << currentUnit->toString() << endl;
            
            // add unprocessed premises to queue for BFS:
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
            
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                // if we haven't processed the current premise yet
                // TODO: remove hack
                if (processed.find(premise) == processed.end() && premise->inference()->rule() != Inference::INPUT)
                {
                    // add it to the queue
                    queue.push(premise);
                }
            }
            
            // if current inference is assigned to A-part
            if (inferenceIsColoredRed(currentUnit))
            {
                Unit* rootOfCurrent = root(unitsToRepresentative, currentUnit);
                parents = InferenceStore::instance()->getParents(currentUnit);
                
                // then for each parent inference,
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    cout << "current premise: " << premise->toString() << endl;

                    // if it is assigned to the B-part
                    if (!inferenceIsColoredRed(premise))
                    {
                        // add the premise (i.e. the antecedent of the parent inference) to upper boundaries of the subproof of currentUnit:
                        unitsToTopBoundaries[rootOfCurrent].push_back(premise); // TODO: this should work since it seems that an empty list is constructed if there was no value for the key before the call.
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
                    if (inferenceIsColoredRed(premise))
                    {
                        Unit* rootOfPremise = root(unitsToRepresentative, premise);

                        // add the premise (i.e. the antecedent of the parent inference) to upper boundaries of the subproof of currentUnit:
                        unitsToBottomBoundaries[rootOfPremise].push_back(premise); // TODO: this should work since it seems that an empty list is constructed if there was no value for the key before the call.
                    }
                }
            }
        }
        
        // we finally have to check for the empty clause, if it appears as boundary of an A-subproof
        ASSERT(root(unitstoRepresentative, refutation) == refutation);

        if (inferenceIsColoredRed(refutation))
        {
            unitsToBottomBoundaries[refutation].push_back(refutation);
        }
        
        
        cout << endl << "unitsToTopBoundaries map:\n";
        for (const auto& keyValuePair : unitsToBottomBoundaries)
        {
            cout << "(" << keyValuePair.first->toString() << ", " << endl;
            for (const auto& element : keyValuePair.second)
            {
                cout << element->toString() << endl;

            }
            
        }
        cout << endl;
        
        /*
         * Part 3: 
         * generate the interpolant (i.e. the splitting formula in the words of the thesis, cf. Definition 3.1.2. of the thesis)
         */
        FormulaList* outerConjunction = FormulaList::empty();
        
        // compute list of subproof representatives by conjoining keys of unitsToTopRepresentatives and unitsToBottomRepresentatives
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
            const std::vector<Unit*>& topBoundaries = unitsToTopBoundaries[root];
            
            FormulaList* conjunction1List = FormulaList::empty();
            for (const auto& boundary : topBoundaries)
            {
                FormulaList::push(boundary->getFormula(), conjunction1List);
            }
            Formula* conjunction1 = JunctionFormula::generalJunction(Connective::AND, conjunction1List);

            // generate conjunction of bottomBoundaries
            const std::vector<Unit*>& bottomBoundaries = unitsToBottomBoundaries[root];

            FormulaList* conjunction2List = FormulaList::empty();
            for (const auto& boundary : bottomBoundaries)
            {
                FormulaList::push(boundary->getFormula(), conjunction2List);
            }
            Formula* conjunction2 = JunctionFormula::generalJunction(Connective::AND, conjunction2List);

            // generate implication "(conj. of topBoundaries) implies (conj. of bottomBoundaries)"
            // NOTE: we perform simplifications of A->B:
            Formula* implication;
            if (conjunction2->connective() == Connective::TRUE)// A->Top => Top
            {
                implication = conjunction2;
            }
            else if (conjunction1->connective() == Connective::TRUE)// Top->B => B
            {
                implication = conjunction2;
            }
            else // no simplification, construct A->B
            {
                FormulaList* implicationList = FormulaList::empty();
                FormulaList::push(new NegatedFormula(conjunction1), implicationList);
                FormulaList::push(conjunction2, implicationList);
                
                implication = JunctionFormula::generalJunction(Connective::OR, implicationList);
            }

            // simplify the arguments for outer conjunction
            if (implication->connective() != Connective::TRUE) // skip argument, since it is redundant
            {
                if (implication->connective() == Connective::FALSE) // if one of the arguments is bottom, the outerConjunction will be bottom
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
 
    bool InterpolantsNew::inferenceIsColoredRed(Kernel::Unit* antecedent)
    {
        // return true,
        // if the antecedent contains a red symbol,
        if (antecedent->getColor() == COLOR_LEFT)
        {
            cout << "coloring " << antecedent->toString() << " red" << endl;
            return true;
        }
        
        // or if any parent contains a red symbol
        VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(antecedent);
        while (parents.hasNext())
        {
            if (parents.next()->getColor() == COLOR_LEFT)
            {
                cout << "coloring " << antecedent->toString() << " red" << endl;
                return true;
            }
        }
        
        // otherwise return false
        cout << "coloring " << antecedent->toString() << " blue" << endl;
        return false;
    }

    
#pragma mark - union find helper methods
  
    Kernel::Unit* InterpolantsNew::root(UnionFindMap& unitsToRepresentative, Unit* unit)
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
    
    void InterpolantsNew::merge(UnionFindMap& unitsToRepresentative, Unit* unit1, Unit* unit2)
    {
        assert(unit1 != unit2);
        Unit* root1 = root(unitsToRepresentative, unit1);
        Unit* root2 = root(unitsToRepresentative, unit2);
        
        unitsToRepresentative[root1] = root2;
    }
}