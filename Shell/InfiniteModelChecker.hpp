/**
 * @file InfiniteModelChecker.hpp
 *
 * Designed to check if the input problem has an infinite model
 * Based on the Infinox prover
 * See https://gupea.ub.gu.se/bitstream/2077/22058/1/gupea_2077_22058_1.pdf
 *
 *
 * @since 28/01/2016 Manchester
 * @author Giles
 */

#ifndef __InfiniteModelChecker__
#define __InfiniteModelChecker__


#include "Forwards.hpp"

namespace Shell {


class InfiniteModelChecker{

public:
static void doCheck(Problem& prb);
static void addCheckingClauses(Problem& prb);
private:
static void addClaimForFunction(TermList x, TermList y, TermList fx, TermList fy, 
                                unsigned arg_srt, unsigned ret_srt, 
                                Formula::VarList* existential,UnitList*& newClauses);


};


}

#endif
