/**
 * @file Infinox.hpp
 *
 * Designed to check if the input problem does not have a finite model
 * Based on the Infinox prover
 * See https://gupea.ub.gu.se/bitstream/2077/22058/1/gupea_2077_22058_1.pdf
 *
 *
 * @since 28/01/2016 Manchester
 * @author Giles
 */

#ifndef __Infinox__
#define __Infinox__


#include "Forwards.hpp"

namespace Shell {


class Infinox{

public:
static void doCheck(Problem& prb);
static void addCheckingClauses(Problem& prb);
private:
static void addClaimForSingleSortFunction(TermList x, TermList y, TermList fx, TermList fy, 
                                unsigned arg_srt, unsigned ret_srt, 
                                Formula::VarList* existential,UnitList*& newClauses);

static void addClaimForMultiSortFunction(TermList x, TermList y, TermList fx, TermList fy,
                                unsigned arg_srt, unsigned ret_srt,
                                Formula::VarList* existential,UnitList*& newClauses);

static void addClaim(Formula* conjecture, UnitList*& newClauses);
static Formula* getName(unsigned fromSrt, unsigned toSrt, bool strict);



};


}

#endif
