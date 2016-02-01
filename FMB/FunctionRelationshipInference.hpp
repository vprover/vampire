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

void findFunctionRelationships(ClauseIterator clauses, DHMap<unsigned,Stack<unsigned>>& injective,
                                                           DHMap<unsigned,Stack<unsigned>>& surjective);

private:

ClauseList* getCheckingClauses();

void addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy,
                         unsigned fname,
                         unsigned arg_srt, unsigned ret_srt, Formula::VarList* existential,
                         ClauseList*& newClauses);

void addClaim(Formula* conjecture, ClauseList*& newClauses);
Formula* getName(unsigned functionName, bool injective);

DHMap<unsigned,unsigned> injectiveMap;
DHMap<unsigned,unsigned> surjectiveMap;

};

}

#endif
