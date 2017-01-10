/**
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#include "Kernel/Formula.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "InterpolantsNew.hpp"

#include "Debug/Assertion.hpp"

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
 *    formula is part of the A-formula or if it is part of the B-formula
 */

namespace Shell
{
    using namespace Kernel;
 
#pragma mark - main methods

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
            processed.insert(currentUnit);
            
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
        
//        cout << endl << "unitsToRepresentative map:\n";
//        for (const auto& keyValuePair : unitsToRepresentative)
//        {
//            cout << "(" << keyValuePair.first->toString() << ", " << keyValuePair.second->toString() << ")" << endl;
//
//        }
//        cout << endl;

        
        /* 
         * Part 2:
         * collect all boundaries of the subproofs
         */
        
        std::unordered_map<Unit*, std::unordered_set<Unit*>> unitsToTopBoundaries; // maps each representative unit of a subproof to the top boundaries of that subproof
        std::unordered_map<Unit*, std::unordered_set<Unit*>> unitsToBottomBoundaries; // maps each representative unit of a subproof to the bottom boundaries of that subproof
        
        processed.clear();
        ASS(queue.empty());
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

                    // if it is assigned to the B-part
                    if (!inferenceIsColoredRed(premise))
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
                    if (inferenceIsColoredRed(premise))
                    {
                        Unit* rootOfPremise = root(unitsToRepresentative, premise);

                        // add the premise (i.e. the conclusion of the parent inference) to upper boundaries of the subproof of currentUnit:
                        unitsToBottomBoundaries[rootOfPremise].insert(premise);
                    }
                }
            }
        }
        
        // we finally have to check for the empty clause, if it appears as boundary of an A-subproof

        if (inferenceIsColoredRed(refutation))
        {
            ASS_EQ(root(unitsToRepresentative, refutation), refutation);
            unitsToBottomBoundaries[refutation].insert(refutation);
        }
        
        
//        cout << endl << "unitsToTopBoundaries map:\n";
//        for (const auto& keyValuePair : unitsToTopBoundaries)
//        {
//            cout << "(" << keyValuePair.first->toString() << "," << endl << "[" << endl;
//            for (const auto& element : keyValuePair.second)
//            {
//                cout << "\t" << element->toString() << endl;
//                
//            }
//            cout << "])";
//        }
//        cout << endl;
//        
//        cout << endl << "unitsToBottomBoundaries map:\n";
//        for (const auto& keyValuePair : unitsToBottomBoundaries)
//        {
//            cout << "(" << keyValuePair.first->toString() << "," << endl << "[" << endl;
//            for (const auto& element : keyValuePair.second)
//            {
//                cout << "\t" << element->toString() << endl;
//                
//            }
//            cout << "])";
//        }
//        cout << endl << endl;
        
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
            const std::unordered_set<Unit*>& topBoundaries = unitsToTopBoundaries[root];
            
            FormulaList* conjunction1List = FormulaList::empty();
            for (const auto& boundary : topBoundaries)
            {
                FormulaList::push(boundary->getFormula(), conjunction1List);
            }
            Formula* conjunction1 = JunctionFormula::generalJunction(Connective::AND, conjunction1List);

            // generate conjunction of bottomBoundaries
            const std::unordered_set<Unit*>& bottomBoundaries = unitsToBottomBoundaries[root];

            FormulaList* conjunction2List = FormulaList::empty();
            for (const auto& boundary : bottomBoundaries)
            {
                FormulaList::push(boundary->getFormula(), conjunction2List);
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
 
    bool InterpolantsNew::inferenceIsColoredRed(Kernel::Unit* conclusion)
    {
        // at first check if inference is an axiom. If yes, assign the inference to the corresponding color
        if (conclusion->inheritedColor() == COLOR_LEFT)
        {
            return true;
        }
        else if (conclusion->inheritedColor() == COLOR_RIGHT)
        {
            return false;
        }
        
        // then check if the inference contains a red symbol (and if yes, assign it to the red partition):
        // - this is the case if either the conclusion contains a red symbol
        if (conclusion->getColor() == COLOR_LEFT)
        {
            cout << "coloring " << conclusion->toString() << " red" << endl;
            return true;
        }
        
        // - or if any parent contains a red symbol
        VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(conclusion);
        while (parents.hasNext())
        {
            if (parents.next()->getColor() == COLOR_LEFT)
            {
                cout << "coloring " << conclusion->toString() << " red" << endl;
                return true;
            }
        }
        
        // in all other cases assign the inference to the blue partition
        // - this is necessary for inferences containing blue symbols
        // - for all other inferences this is a decision we make for this simple version of splitting function
        cout << "coloring " << conclusion->toString() << " blue" << endl;
        return false;
    }

    
#pragma mark - union find helper methods
  
    Kernel::Unit* InterpolantsNew::root(UnionFindMap& unitsToRepresentative, Unit* unit)
    {
        Unit* root = unit;
        while (unitsToRepresentative.find(root) != unitsToRepresentative.end())
        {
            ASS_NEQ(unitsToRepresentative.at(root), root);
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
        ASS_NEQ(unit1, unit2);
        Unit* root1 = root(unitsToRepresentative, unit1);
        Unit* root2 = root(unitsToRepresentative, unit2);
        
        if (root1 != root2) // we could also add elements as their own roots, but this is not necessary.
        {
            unitsToRepresentative[root2] = root1;
        }
    }
}