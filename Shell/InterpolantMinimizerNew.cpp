/**
 * @file InterpolantMinimizerNew.cpp
 * Implements class InterpolantMinimizerNew.
 * @author Bernhard Gleiss
 */

#if VZ3

#include "InterpolantMinimizerNew.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include <memory>
#include <unordered_set> // TODO: remove this after benchmarking
#include "z3++.h"

namespace Shell
{
    using namespace Kernel;

    std::unordered_map<Kernel::Unit*, Kernel::Color> InterpolantMinimizerNew::computeSplittingFunction(Kernel::Unit* refutation,  UnitWeight weightFunction)
    {
        CALL("InterpolantMinimizerNew::computeSplittingFunction");

        using namespace z3;
        context c;
        optimize solver(c);
        
        std::unordered_map<Unit*, std::unique_ptr<expr>> unitsToExpressions; // needed in order to map the result of the optimisation-query back to the inferences.
        std::unordered_map<Unit*, std::unique_ptr<expr>> unitsToPenalties;
        int i = 0; // counter needed for unique names
        
        // note: idea from the thesis: we use x_i to denote whether inference i is assigned to the A-part.
        ProofIteratorPostOrder it(refutation);
        while (it.hasNext()) // traverse the proof in depth-first post order
        {
            Unit* current = it.next();
            
            // construct a new expression representing the current inference and
            // remember that the current inference is encoded by that expression
            std::unique_ptr<expr> x_i_ptr (new expr(c));
            *x_i_ptr = c.bool_const(("x_" + std::to_string(i)).c_str()); // ugly but necessary due to z3-API
            unitsToExpressions.emplace(std::make_pair(current, std::move(x_i_ptr)));
            
            
            std::unique_ptr<expr> p_i_ptr (new expr(c));
            *p_i_ptr = c.bool_const(("p_" + std::to_string(i)).c_str()); // ugly but necessary due to z3-API
            unitsToPenalties.emplace(std::make_pair(current, std::move(p_i_ptr)));
            
            // construct variable which encodes soft constraints
            expr& p_i = *unitsToPenalties[current];
            double weight = weightForUnit(current, weightFunction);
            solver.add(!p_i, c.real_val(std::to_string(weight).c_str()));
            
            i++;
            
            expr& x_i = *unitsToExpressions.at(current);
            // if inference is an axiom we need to assign it to the corresponding partition
            if (current->inheritedColor() == COLOR_LEFT)
            {
                solver.add(x_i);
            }
            else if (current->inheritedColor() == COLOR_RIGHT)
            {
                solver.add(!x_i);
            }
            
            // if the conclusion contains a colored symbol, we need to assign the inference to the corresponding partition
            if (current->getColor() == COLOR_LEFT)
            {
                solver.add(x_i);
            }
            else if (current->getColor() == COLOR_RIGHT)
            {
                solver.add(!x_i);
            }
            
            // if any parent contains a colored symbol, we need to assign the inference to the corresponding partition
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                if (premise->getColor() == COLOR_LEFT)
                {
                    solver.add(x_i);
                }
                else if (premise->getColor() == COLOR_RIGHT)
                {
                    solver.add(!x_i);
                }
            }
            
            // now add the main constraints: the conclusion of a parent-inference is included in the interpolant iff the
            // the parent inference is assigned a different partition than the current inference
            parents = InferenceStore::instance()->getParents(current);
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                expr& x_j = *unitsToExpressions[premise];
                expr& p_j = *unitsToPenalties[premise];
                
                solver.add(!(x_i != x_j) || p_j);
            }
        }

        // we are now finished with adding constraints, so use z3 to compute an optimal model
        solver.check();

        // and convert computed model to splitting function
        model m = solver.get_model();
        
        std::unordered_map<Kernel::Unit*, Kernel::Color> splittingFunction;
        for (const auto& keyValuePair : unitsToExpressions)
        {
            Unit* current = keyValuePair.first;
            expr evaluation = m.eval(*unitsToExpressions[current]);
            
            if (Z3_get_bool_value(c,evaluation) == Z3_L_TRUE)
            {
                splittingFunction[current] = COLOR_LEFT;
            }
            else
            {
                splittingFunction[current] = COLOR_RIGHT;
            }
        }
        
        return splittingFunction;
    }
    
    void InterpolantMinimizerNew::analyzeLocalProof(Kernel::Unit *refutation)
    {
        BYPASSING_ALLOCATOR;
        CALL("InterpolantMinimizerNew::analyzeLocalProof");

        // print statistics on grey area
        analyzeGreyAreas(refutation);
        
        // compute number of red subproofs
        const std::unordered_map<Unit*, Color> splittingFunction = computeSplittingFunction(refutation, UnitWeight::VAMPIRE);
        const std::unordered_map<Unit*, Unit*> unitsToRepresentative = computeSubproofs(refutation, splittingFunction);
        
        std::unordered_set<Unit*> representatives;
        for (const auto& keyValuePair : unitsToRepresentative)
        {
            representatives.insert(keyValuePair.second);
        }
        cout << "Number of red subproofs: " << representatives.size() << endl;
    }
    
    /*
     * compute both number of inferences which are necessarily assigned to red and to blue, and number of inferences which can be assigned arbitrarily
     * computes percentage grey / (red + blue + grey)
     */
    void InterpolantMinimizerNew::analyzeGreyAreas(Kernel::Unit* refutation)
    {
        CALL("InterpolantMinimizerNew::analyzeGreyArea");
        
        int number_red = 0;
        int number_blue = 0;
        int number_grey = 0;
        
        /*
         * note: reuses code from heuristic splitting function
         */
        ProofIteratorPostOrder it(refutation);
        while (it.hasNext()) // traverse the proof in depth-first post order
        {
            Unit* current = it.next();
            ASS((!InferenceStore::instance()->getParents(current).hasNext() && (current->inheritedColor() == COLOR_LEFT || current->inheritedColor() == COLOR_RIGHT)) || (InferenceStore::instance()->getParents(current).hasNext() &&  current->inheritedColor() == COLOR_INVALID));
            
            // if the inference is an axiom, assign it to the corresponding partition
            if (!InferenceStore::instance()->getParents(current).hasNext())
            {
                if (current->inheritedColor() == COLOR_LEFT)
                {
                    number_red++;
                }
                else
                {
                    number_blue++;
                }
                continue;
            }
            
            // if the inference contains a colored symbol, assign it to the corresponding partition (this
            // ensures requirement of a LOCAL splitting function in the words of the thesis):
            // - this is the case if either the conclusion contains a colored symbol
            if (current->getColor() == COLOR_LEFT)
            {
                number_red++;
                continue;
            }
            else if (current->getColor() == COLOR_RIGHT)
            {
                number_blue++;
                continue;
            }
            
            // - or if any premise contains a colored symbol
            Color containedColor = COLOR_TRANSPARENT;
            VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                if (premise->getColor() == COLOR_LEFT || premise->getColor() == COLOR_RIGHT)
                {
                    containedColor = premise->getColor();
                    break;
                }
            }
            if (containedColor == COLOR_LEFT)
            {
                number_red++;
                continue;
            }
            else if (containedColor == COLOR_RIGHT)
            {
                number_blue++;
                continue;
            }
            
            /* otherwise we choose the following heuristic
             * if the weighted sum of the conclusions of all parent inferences assigned
             * to the red partition is greater than the weighted sum of the conclusions
             * of all parent inferences assigned to the blue partition, then
             * assign the inference to red, otherwise to blue
             */
            number_grey++;
        }
        
        cout << "Proof contains " << number_red << " / " << number_blue << " / " << number_grey << " inferences (red/blue/grey)" << endl;
        cout << "Percentage of grey inferences: " << static_cast<double>(number_grey) / (number_red + number_blue + number_grey) << endl;
    }

}

#endif // VZ3
