/**
 * @file InterpolantMinimizerNew.cpp
 * Implements class InterpolantMinimizerNew.
 * @author Bernhard Gleiss
 */

//#if VZ3

#include "InterpolantMinimizerNew.hpp"

#include "Kernel/Unit.hpp"
#include "Kernel/InferenceStore.hpp"

#include "z3++.h"

namespace Shell
{
    using namespace Kernel;
    
    void InterpolantMinimizerNew::computeSplittingFunction(Kernel::Unit* refutation,  UnitWeight weightFunction)
    {
        using namespace z3;
        context c;
        optimize solver(c);
        
        std::unordered_map<Unit*, std::unique_ptr<expr>> unitsToExpressions; // needed in order to map the result of the optimisation-query back to the inferences.

        int i = 0; // counter needed for unique names
        
        std::stack<Unit*> stack;
        stack.push(refutation);
        std::unordered_set<Unit*> processed; // keep track of already visited units.

        // note: idea from the thesis: we use x_i to denote whether inference i is assigned to the A-part.
        // iterative DFS (post-order) through the proof DAG
        while (!stack.empty())
        {
            Unit* currentUnit = stack.top();

            // if we haven't already visited current unit
            if (processed.find(currentUnit) == processed.end())
            {
                bool existsUnvisitedParent = false;

                // add premises to stack for DFS:
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
                
                while (parents.hasNext())
                {
                    Unit* premise= parents.next();
                    
                    // if we haven't processed the current premise yet
                    if (processed.find(premise) == processed.end())
                    {
                        // add it to the stack
                        stack.push(premise);
                        
                        existsUnvisitedParent = true;
                    }
                }
                
                if (!existsUnvisitedParent)
                {
                    processed.insert(currentUnit);
                    
                    // construct a new expression representing the current inference and
                    // remember that the current inference is encoded by that expression
                    std::unique_ptr<expr> x_i_ptr (new expr(c));
                    *x_i_ptr = c.bool_const(("x_" + std::to_string(i)).c_str()); // ugly but necessary due to z3-API
                    unitsToExpressions.emplace(std::make_pair(currentUnit, std::move(x_i_ptr)));
                    i++;
                    
                    expr& x_i = *unitsToExpressions.at(currentUnit);
                    // if inference is an axiom we need to assign it to the corresponding partition
                    if (currentUnit->inheritedColor() == COLOR_LEFT)
                    {
                        solver.add(x_i);
                    }
                    else if (currentUnit->inheritedColor() == COLOR_RIGHT)
                    {
                        solver.add(!x_i);
                    }
                    
                    // if the conclusion contains a colored symbol, we need to assign the inference to the corresponding partition
                    if (currentUnit->getColor() == COLOR_LEFT)
                    {
                        solver.add(x_i);
                    }
                    else if (currentUnit->getColor() == COLOR_RIGHT)
                    {
                        solver.add(!x_i);
                    }
                    
                    // if any parent contains a colored symbol, we need to assign the inference to the corresponding partition
                    parents = InferenceStore::instance()->getParents(currentUnit);
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
                    parents = InferenceStore::instance()->getParents(currentUnit);
                    while (parents.hasNext())
                    {
                        Unit* premise= parents.next();
                        
                        assert(unitsToExpressions.find(premise) != unitsToExpressions.end());
                        expr& x_j = *unitsToExpressions[premise];
                        
                        double weight = weightForUnit(premise, weightFunction);
                        solver.add(x_i == x_j, c.real_val(std::to_string(weight).c_str())); // TODO: add actual weight here! cf. addCostFormula()-function from Interpolants.cpp
                    }
                    
                    stack.pop();
                }
            }
            else
            {
                stack.pop();
            }
        }
        
        // we are now finished with adding constraints, so use z3 to compute an optimal model
        solver.check();
        
        // and convert computed model to splitting function
        model m = solver.get_model();
        
        for (const auto& keyValuePair : unitsToExpressions)
        {
            Unit* currentUnit = keyValuePair.first;
            expr evaluation = m.eval(*unitsToExpressions[currentUnit]);
            
            if (Z3_get_bool_value(c,evaluation) == Z3_L_TRUE)
            {
                //cout << "coloring " << currentUnit->toString() << "red" << endl;
                currentUnit->setInheritedColor(COLOR_LEFT);
            }
            else
            {
                //cout << "coloring " << currentUnit->toString() << "blue" << endl;
                currentUnit->setInheritedColor(COLOR_RIGHT);
            }
        }
    }
}

//#endif // VZ3
