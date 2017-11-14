
/*
 * File FunctionRelationshipInference.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file FunctionRelationshipInference.hpp
 * Defines class for finite models
 *
 * @since 01/02/2016 Manchester
 * @author Giles
 */

#ifndef __FunctionRelationshipInference__
#define __FunctionRelationshipInference__

#include "Forwards.hpp"



namespace FMB {

using namespace Lib;
using namespace Kernel;

/**
 *
 *
 */
class FunctionRelationshipInference {

public:

void findFunctionRelationships(ClauseIterator clauses, 
                               Stack<DHSet<unsigned>*>& eq_classes, 
                               DHSet<std::pair<unsigned,unsigned>>& nonstrict_cons,
                               DHSet<std::pair<unsigned,unsigned>>& strict_cons); 

private:

ClauseList* getCheckingClauses();

void addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy,
                         unsigned fname,
                         unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential,
                         ClauseList*& newClauses);

void addClaim(Formula* conjecture, ClauseList*& newClauses);
Formula* getName(unsigned fromSort, unsigned toSort, bool strict);

DHMap<unsigned,std::pair<unsigned,unsigned>> _labelMap_nonstrict;
DHMap<unsigned,std::pair<unsigned,unsigned>> _labelMap_strict;

};

}

#endif
