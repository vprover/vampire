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
 * @file InterpolantsNew.cpp
 * Implements class InterpolantsNew.
 * @author Bernhard Gleiss
 */

#include "InterpolantsNew.hpp"

#include <unordered_set>

#include "Kernel/Unit.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/InferenceStore.hpp"

#include "Shell/Flattening.hpp"
#include "SimplifyFalseTrue.hpp"
#include "Shell/NNF.hpp"

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
 *    formula is part of the A-formula, part of the B-formula or part of the
 *    theory axioms (COLOR_LEFT, COLOR_RIGHT or COLOR_TRANSPARENT).
 *    For all other formulas, inheritedColor() is set to COLOR_INVALID
 * ========================================================================
 * Note that the word 'splitting' is used with two different meanings in
 * this class: 1) splitting a proof into an A- and a B- part as described
 *                in the thesis
 *             2) splitting the proof for Avatar
 */

namespace Shell
{
    using namespace Kernel;
    
    
//preprocessing proof
    
    void InterpolantsNew::removeTheoryInferences(Unit* refutation)
    {
        BYPASSING_ALLOCATOR;
        CALL("InterpolantsNew::removeTheoryInferences");

        ProofIteratorPostOrder it(refutation);
        while (it.hasNext()) // traverse the proof in depth-first post order
        {
            Unit* current = it.next();

            // sanity check
            ASS((!InferenceStore::instance()->getParents(current).hasNext() &&  (   current->inheritedColor() == COLOR_LEFT
                                                                                        || current->inheritedColor() == COLOR_RIGHT
                                                                                        || current->inheritedColor() == COLOR_TRANSPARENT
                                                                                        ))
                   || (InferenceStore::instance()->getParents(current).hasNext() &&  current->inheritedColor() == COLOR_INVALID));

            // compute whether inference has grey and non-grey parent inferences
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
                
                current->inference() = NonspecificInferenceMany(current->inference().rule(), premises);
            }
        }
    }
    
    
//main method

    /*
     * main method
     * cf. Definition 3.1.2 of the thesis
     */
    Formula* InterpolantsNew::getInterpolant(Unit *refutation, UnitWeight weightFunction)
    {
        BYPASSING_ALLOCATOR;
        CALL("InterpolantsNew::getInterpolant");
                
        /*
         * compute coloring for the inferences, i.e. compute splitting function in the words of the thesis
         */
        const SplittingFunction splittingFunction = computeSplittingFunction(refutation, weightFunction);
        
        /*
         * compute A-subproofs
         */
        const SubproofsUnionFind unitsToRepresentative = computeSubproofs(refutation, splittingFunction);
        
        /*
         * collect all boundaries of the subproofs
         */
        const Boundary boundary = computeBoundary(refutation, splittingFunction);
        
        /*
         * generate the interpolant (i.e. the splitting formula in the words of the thesis, cf. Definition 3.1.2. of the thesis)
         */
        const auto interpolant = generateInterpolant(refutation, boundary, splittingFunction, unitsToRepresentative);
        
        return interpolant;
    }
    
    
//main helper methods
    
    /*
     * compute the maximal A-subproofs of the proofs using standard union-find ideas as described in the thesis
     * Note: can't just use depth-first-search, since edge information is only saved in one direction in the nodes
     * Note: We represent each subproof by the conclusion of one of its inferences (the so called representative unit)
     */
    InterpolantsNew::SubproofsUnionFind InterpolantsNew::computeSubproofs(Unit* refutation, const SplittingFunction& splittingFunction)
    {
        CALL("InterpolantsNew::computeSubproofs");

        std::unordered_map<Unit*, Unit*> unitsToRepresentative; // maps each unit u1 (belonging to a red subproof) to the representative unit u2 of that subproof
        std::unordered_map<Unit*, int> unitsToSize; // needed for weighted quick-union: for each unit, counts number of elements rooted in that unit
        
        ProofIteratorBFSPreOrder it(refutation); // traverse the proof in breadth-first pre-order
        while (it.hasNext())
        {
            Unit* current = it.next();
            
            // standard union-find: if current inference is assigned to A-part of the proof,
            if (splittingFunction.at(current) == COLOR_LEFT)
            {
                // then for each parent inference,
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // the parent may be from the B-part, this is to induce connectedness over a common parent
                    // (Even then we want to merge, so that this parent appears only once in the final interpolant.)
                    {
                        // merge the subproof of the current inference with the subproof of the parent inference
                        merge(unitsToRepresentative, unitsToSize, current, premise);
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
    InterpolantsNew::Boundary InterpolantsNew::computeBoundary(Unit* refutation,const SplittingFunction& splittingFunction)
    {
        CALL("InterpolantsNew::computeBoundary");

        std::unordered_set<Kernel::Unit*> inputNodes;   // input is a blue premise of a red inference
        std::unordered_set<Kernel::Unit*> outputNodes;  // output is a red premise of a blue inference or a red refutation
        
        ProofIteratorBFSPreOrder it(refutation); // traverse the proof in breadth-first pre-order
        while (it.hasNext())
        {
            Unit* current = it.next();
            
            // if current inference is assigned to A-part
            ASS(splittingFunction.at(current) == COLOR_LEFT || splittingFunction.at(current) == COLOR_RIGHT);
            if (splittingFunction.at(current) == COLOR_LEFT)
            {
                // then for each parent inference,
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // if it is assigned to the B-part
                    ASS(splittingFunction.at(premise) == COLOR_LEFT || splittingFunction.at(premise) == COLOR_RIGHT);
                    if (splittingFunction.at(premise) != COLOR_LEFT)
                    {
                        inputNodes.insert(premise);
                    }
                }
            }
            
            // if current inference is assigned to B-part
            else
            {
                // then for each parent inference,
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);
                while (parents.hasNext())
                {
                    Unit* premise = parents.next();
                    
                    // if it is assigned to the A-part
                    ASS(splittingFunction.at(premise) == COLOR_LEFT || splittingFunction.at(premise) == COLOR_RIGHT);
                    if (splittingFunction.at(premise) == COLOR_LEFT)
                    {
                        outputNodes.insert(premise);
                    }
                }
            }
        }

        // we finally have to check for the empty clause, if it appears as boundary of an A-subproof
        if (splittingFunction.at(refutation) == COLOR_LEFT)
        {
            outputNodes.insert(refutation);
        }

        return make_pair(std::move(inputNodes), std::move(outputNodes));
    }
    
    /*
     * generate the interpolant from the boundary
     * Note: we already have collected all relevant information before calling this function, 
     * we now just need to build (and simplify) a formula out of the information.
     */
    Formula* InterpolantsNew::generateInterpolant(Kernel::Unit* refutation, const Boundary& boundary,
                const SplittingFunction& splittingFunction, const SubproofsUnionFind& unitsToRepresentative)
    {
        CALL("InterpolantsNew::generateInterpolant");

        const std::unordered_set<Unit*>& inputNodes = boundary.first;
        const std::unordered_set<Unit*>& outputNodes = boundary.second;
        
        struct InterpolantBuilder {
          int implCnt; // for statistics only

          Kernel::Color lastCol;
          FormulaList* conjuncts;
          Formula* aside;
          InterpolantBuilder() : implCnt(0), lastCol(COLOR_LEFT), conjuncts(FormulaList::empty()), aside(nullptr) {}

          Formula* finiliseLeft() {
            CALL("InterpolantsNew::InterpolantBuilder::finiliseLeft");
            return JunctionFormula::generalJunction(Connective::AND, conjuncts);
          }

          Formula* finiliseRight() {
            CALL("InterpolantsNew::InterpolantBuilder::finiliseRight");
            Formula* antecedent = JunctionFormula::generalJunction(Connective::AND, conjuncts);

            implCnt++;

            return new BinaryFormula(IMP,antecedent,aside);
          }

          Formula* finalise() {
            CALL("InterpolantsNew::InterpolantBuilder::finalise");
            if (lastCol == COLOR_LEFT) {
              return finiliseLeft();
            } else {
              return finiliseRight();
            }
          }

          void addLeft(Unit* u) {
            CALL("InterpolantsNew::InterpolantBuilder::addLeft");
            // cout << "addLeft " << u->toString() << endl;

            if (lastCol != COLOR_LEFT) {
              Formula* f = finiliseRight();
              conjuncts = FormulaList::empty();
              FormulaList::push(f,conjuncts);
            }
            FormulaList::push(u->getFormula(),conjuncts);

            lastCol = COLOR_LEFT;
          }

          void addRight(Unit* u) {
            CALL("InterpolantsNew::InterpolantBuilder::addRight");
            // cout << "addRight " << u->toString() << endl;

            if (lastCol != COLOR_RIGHT) {
              aside = finiliseLeft();
              conjuncts = FormulaList::empty();
            }
            FormulaList::push(u->getFormula(),conjuncts);

            lastCol = COLOR_RIGHT;
          }
        };

        // one nested implication for each connected A-part
        // std::unordered_map<Unit*, InterpolantBuilder> contributions;
        InterpolantBuilder justOneNoodle;

        // do dfs on the derivation and present results in the reversed order (using stack for it)
        ProofIteratorPostOrder pipo(refutation);
        static UnitStack buffer;
        buffer.reset();
        buffer.loadFromIterator(pipo);

        UnitStack::Iterator it(buffer);
        while (it.hasNext()) {
          Unit* u = it.next();

          // cout << "Next " << u->toString() << endl;

          if (outputNodes.find(u) != outputNodes.end()) {
            ASS_EQ(splittingFunction.at(u),COLOR_LEFT);

            /*
            Unit* uRoot = root(unitsToRepresentative, u);
            contributions[uRoot].addLeft(u);
            */
            justOneNoodle.addLeft(u);

          } else if (inputNodes.find(u) != inputNodes.end()) {
            ASS_EQ(splittingFunction.at(u),COLOR_RIGHT);

            /*
            Unit* uRoot = root(unitsToRepresentative, u);
            contributions[uRoot].addRight(u);
            */
            justOneNoodle.addRight(u);
          }
        }

        /*
        FormulaList* outerConjunction = FormulaList::empty();

        // statistics only
        vstring nestednesses;

        for (auto& rootBuilderPair : contributions) {
          InterpolantBuilder& builder = rootBuilderPair.second;

          FormulaList::push(builder.finalise(),outerConjunction);

          nestednesses += Int::toString(builder.implCnt) + ",";
        }
        */

        // finally conjoin all generated implications and return the simplified result, which is the interpolant
        //Formula* interpolant = JunctionFormula::generalJunction(Connective::AND, outerConjunction);
        Formula* interpolant = justOneNoodle.finalise();
        
        // print number of pieces
        // print the depth of each ...

        // cout << "Number of red components: " << contributions.size() << endl;
        cout << "Nestedness: " << justOneNoodle.implCnt << endl;
        cout << "Before simplification: " << interpolant->toString() << endl;
        cout << "Weight before simplification: " << interpolant->weight() << endl;

        return Flattening::flatten(NNF::ennf(Flattening::flatten(SimplifyFalseTrue::simplify(interpolant)),true));
    }


    // splitting function
 
    /*
     * implements local splitting function from the thesis (improved version of approach #2, cf. section 3.3)
     */
    std::unordered_map<Kernel::Unit*, Kernel::Color> InterpolantsNew::computeSplittingFunction(Kernel::Unit* refutation, UnitWeight weightFunction)
    {
        CALL("InterpolantsNew::computeSplittingFunction");

        std::unordered_map<Kernel::Unit*, Kernel::Color> splittingFunction;
        
        ProofIteratorPostOrder it(refutation);
        while (it.hasNext()) // traverse the proof in depth-first post order
        {
            Unit* current = it.next();
            ASS((!InferenceStore::instance()->getParents(current).hasNext() && (current->inheritedColor() == COLOR_LEFT || current->inheritedColor() == COLOR_RIGHT)) || (InferenceStore::instance()->getParents(current).hasNext() &&  current->inheritedColor() == COLOR_INVALID));

            // if the inference is an axiom, assign it to the corresponding partition
            if (!InferenceStore::instance()->getParents(current).hasNext())
            {
                splittingFunction[current] = current->inheritedColor();
                continue;
            }
            
            // if the inference contains a colored symbol, assign it to the corresponding partition (this
            // ensures requirement of a LOCAL splitting function in the words of the thesis):
            // - this is the case if either the conclusion contains a colored symbol
            if (current->getColor() == COLOR_LEFT || current->getColor() == COLOR_RIGHT)
            {
                splittingFunction[current] = current->getColor();
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
            if (containedColor != COLOR_TRANSPARENT)
            {
                splittingFunction[current] = containedColor;
                continue;
            }
            
            /* otherwise we choose the following heuristic
             * if the weighted sum of the conclusions of all parent inferences assigned
             * to the red partition is greater than the weighted sum of the conclusions
             * of all parent inferences assigned to the blue partition, then
             * assign the inference to red, otherwise to blue
             */
            parents = InferenceStore::instance()->getParents(current);
            
            double difference = 0;
            while (parents.hasNext())
            {
                Unit* premise= parents.next();
                
                ASS(splittingFunction.at(premise) == COLOR_LEFT || splittingFunction.at(premise) == COLOR_RIGHT);
                if (splittingFunction.at(premise) == COLOR_LEFT)
                {
                    difference += weightForUnit(premise, weightFunction);
                }
                else
                {
                    difference -= weightForUnit(premise, weightFunction);
                }
            }
            splittingFunction[current] = difference > 0 ? COLOR_LEFT : COLOR_RIGHT;
        }
        
        return splittingFunction;
    }

// helper method for unit weight

    double InterpolantsNew::weightForUnit(Kernel::Unit* unit, UnitWeight weightFunction)
    {
        CALL("InterpolantsNew::weightForUnit");

        if (weightFunction == UnitWeight::VAMPIRE)
        {
            return unit->getWeight();
        }
        else
        {
            ASS_EQ(weightFunction, UnitWeight::QUANTIFIED_VARS);
            return unit->varCnt();
        }
    }


// union find helper methods
    
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
        CALL("InterpolantsNew::root");

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
        CALL("InterpolantsNew::find");

        return root(unitsToRepresentative, unit1) == root(unitsToRepresentative, unit2);
    }
    
    void InterpolantsNew::merge(UnionFindMap& unitsToRepresentative,
                                std::unordered_map<Unit*, int> unitsToSize,
                                Unit* unit1,
                                Unit* unit2)
    {
        CALL("InterpolantsNew::merge");

        ASS_NEQ(unit1, unit2);
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

    ProofIteratorBFSPreOrder::ProofIteratorBFSPreOrder(Unit* refutation)
    {
        CALL("ProofIteratorBFSPreOrder::ProofIteratorBFSPreOrder");

        todo.push(refutation);
    }

    bool ProofIteratorBFSPreOrder::hasNext()
    {
        CALL("ProofIteratorBFSPreOrder::hasNext");

        while (!todo.empty())
        {
            if (visited.find(todo.front()) == visited.end())
            {
                return true;
            }
            else
            {
                todo.pop();
            }
        }

        return false;
    }

    /*
     * iterative Breadth-first search (BFS) through the proof DAG
     */
    Unit* ProofIteratorBFSPreOrder::next()
    {
        CALL("ProofIteratorBFSPreOrder::next");

        while (!todo.empty())
        {
            Unit* current = todo.front();
            todo.pop();

            if (visited.find(current) == visited.end())
            {
                // add unprocessed premises to queue for BFS:
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(current);

                while (parents.hasNext())
                {
                    Unit* premise= parents.next();
                    todo.push(premise);
                }

                // remember that we have visited current
                visited.insert(current);

                return current;
            }

        }

        // we have already iterated through all inferences
        return nullptr;
    }


    ProofIteratorPostOrder::ProofIteratorPostOrder(Unit* refutation)
    {
        CALL("ProofIteratorPostOrder::ProofIteratorPostOrder");
        todo.push(refutation);
    }

    bool ProofIteratorPostOrder::hasNext()
    {
        CALL("ProofIteratorPostOrder::hasNext");
        return !todo.empty();
    }

    /*
     * iterative post-order depth-first search (DFS) through the proof DAG
     * following the usual ideas, e.g.
     * https://pythonme.wordpress.com/2013/08/05/algorithm-iterative-dfs-depth-first-search-with-postorder-and-preorder/
     */
    Unit* ProofIteratorPostOrder::next()
    {
        CALL("ProofIteratorPostOrder::next");
        while (!todo.empty())
        {
            Unit* currentUnit = todo.top();

            // if we haven't already visited the current unit
            if (visited.find(currentUnit) == visited.end())
            {
                bool existsUnvisitedParent = false;

                // add unprocessed premises to stack for DFS. If there is at least one unprocessed premise, don't compute the result
                // for currentUnit now, but wait until those unprocessed premises are processed.
                VirtualIterator<Unit*> parents = InferenceStore::instance()->getParents(currentUnit);
                while (parents.hasNext())
                {
                    Unit* premise= parents.next();

                    // if we haven't visited the current premise yet
                    if (visited.find(premise) == visited.end())
                    {
                        // add it to the stack
                        todo.push(premise);
                        existsUnvisitedParent = true;
                    }
                }

                // if we already visited all parent-inferences, we can visit the inference too
                if (!existsUnvisitedParent)
                {
                    visited.insert(currentUnit);
                    todo.pop();
                    return currentUnit;
                }
            }
            else
            {
                todo.pop();
            }
        }

        // we have already iterated through all inferences
        return nullptr;
    }


}
