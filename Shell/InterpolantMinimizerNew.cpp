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
                
                assert(unitsToExpressions.find(premise) != unitsToExpressions.end());
                expr& x_j = *unitsToExpressions[premise];
                
                double weight = weightForUnit(premise, weightFunction);
                solver.add(x_i == x_j, c.real_val(std::to_string(weight).c_str())); // TODO: add actual weight here! cf. addCostFormula()-function from Interpolants.cpp
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
}

#endif // VZ3
