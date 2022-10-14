/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "SATSubsumption/SATSubsumptionResolution.hpp"
#include "SATSubsumption/Util.hpp"
#include "Kernel/Inference.hpp"

using namespace std;
using namespace SMTSubsumption;

static SATSubsumption::MatchSet *matchSet;
static vvector<SATSubsumption::Match*> matches;

#define SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION \
  DECL_DEFAULT_VARS                  \
  DECL_VAR(x1,1)                     \
  DECL_VAR(x2,2)                     \
  DECL_VAR(x3,3)                     \
  DECL_VAR(y1,4)                     \
  DECL_SORT(s)                       \
  DECL_CONST(c, s)                   \
  DECL_CONST(d, s)                   \
  DECL_CONST(e, s)                   \
  DECL_FUNC(f, {s}, s)            \
  DECL_FUNC(g, {s}, s)               \
  DECL_PRED(p, {s})                  \
  DECL_PRED(p2, {s, s})                  \
  DECL_PRED(q, {s})                  \
  DECL_PRED(r, {s})                  \

static void setupMatchSet()
{
  matchSet = new SATSubsumption::MatchSet(3, 3);
  matches = vvector<SATSubsumption::Match*>();

    // Try to allocated 3 matches for the first literal
    SATSubsumption::Match* match1 = matchSet->allocateMatch();
    SATSubsumption::Match* match2 = matchSet->allocateMatch();
    SATSubsumption::Match* match3 = matchSet->allocateMatch();

    ASS(match1 != nullptr);
    ASS(match2 != nullptr);
    ASS(match3 != nullptr);
    ASS(match1 != match2);
    ASS(match1 != match3);
    ASS(match2 != match3);

    match1->_baseLitIndex = 0;
    match1->_instanceLitIndex = 0;
    match1->_isPositive = true;
    match1->_satVar = subsat::Var(0);

    match2->_baseLitIndex = 2;
    match2->_instanceLitIndex = 1;
    match2->_isPositive = false;
    match2->_satVar = subsat::Var(1);

    match3->_baseLitIndex = 2;
    match3->_instanceLitIndex = 2;
    match3->_isPositive = true;
    match3->_satVar = subsat::Var(2);

    matches.push_back(match1);
    matches.push_back(match2);
    matches.push_back(match3);
}

static void teardownMatchSet()
{
  delete matchSet;
  matches.clear();
}

static bool vectorContains(vvector<SATSubsumption::Match*> vec, SATSubsumption::Match* match)
{
    for (auto m : vec) {
        if (m == match) {
            return true;
        }
    }
    return false;
}

static void checkConsistency()
{
    ASS(matchSet->getAllMatches().size() == matches.size());
    for (auto match : matches) {
        ASS(vectorContains(matchSet->getMatchesForBaseLit(match->_baseLitIndex), match));
        ASS(vectorContains(matchSet->getMatchesForInstanceLit(match->_instanceLitIndex), match));
        ASS(matchSet->getMatchForVar(match->_satVar) == match);
        ASS(vectorContains(matchSet->getAllMatches(), match));
    }
}

TEST_FUN(MatcheSetIndexing)
{
    setupMatchSet();
    // Add the matches to the match set

    // Check that the matches are in the correct indices
    checkConsistency();
    teardownMatchSet();
}

/**
 * Check that the resiwing of the set does not destroy the matches
 */
TEST_FUN(MatcheSetResize)
{
    setupMatchSet();
    // Add the matches to the match set
    for (auto match : matches) {
        matchSet->addMatch(match);
    }
    checkConsistency();
    matchSet->resize(4, 5);
    checkConsistency();
    teardownMatchSet();
}

static void checkStateI(unsigned i, bool positive, bool negative)
{
    if (positive != matchSet->hasPositiveMatchForBaseLit(i)) {
        cerr << "Positive match for I " << i << " should be " << positive << endl;
    } else if(negative != matchSet->hasNegativeMatchForBaseLit(i)) {
        cerr << "Negative match for I " << i << " should be " << negative << endl;
    } else {
        return;
    } ASS(false);
}

static void checkStateJ(unsigned j, bool positive, bool negative)
{
    if (positive != matchSet->hasPositiveMatchForInstanceLit(j)) {
        cerr << "Positive match for J " << j << " should be " << positive << endl;
    } else if(negative != matchSet->hasNegativeMatchForInstanceLit(j)) {
        cerr << "Negative match for J " << j << " should be " << negative << endl;
    } else {
        return;
    } ASS(false);
}


TEST_FUN(TestSetBitTricks)
{
    unsigned n = 3;
    unsigned m = 5;
    vvector<bool> iInserted(n, false);
    vvector<bool> jInserted(m, false);
    matchSet = new SATSubsumption::MatchSet(n, m);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            SATSubsumption::Match* match1 = matchSet->allocateMatch();
            *match1 = SATSubsumption::Match(i, j, true, subsat::Var(0));
            matchSet->addMatch(match1);

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(k, iInserted[k], false);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(k, jInserted[k], false);
            }
        }
    }
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            SATSubsumption::Match* match1 = matchSet->allocateMatch();
            *match1 = SATSubsumption::Match(i, j, false, subsat::Var(0));
            matchSet->addMatch(match1);

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(k, true, iInserted[k]);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(k, true, jInserted[k]);
            }
        }
    }
    matchSet->clear();
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            SATSubsumption::Match* match1 = matchSet->allocateMatch();
            *match1 = SATSubsumption::Match(i, j, false, subsat::Var(0));
            matchSet->addMatch(match1);

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(k, false, iInserted[k]);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(k, false, jInserted[k]);
            }
        }
    }
    iInserted = vvector<bool>(n, false);
    jInserted = vvector<bool>(m, false);
    for (unsigned i=0; i<n; i++) {
        for (unsigned j=0; j<m; j++) {
            SATSubsumption::Match* match1 = matchSet->allocateMatch();
            *match1 = SATSubsumption::Match(i, j, true, subsat::Var(0));
            matchSet->addMatch(match1);

            iInserted[i] = true;
            jInserted[j] = true;
            for (unsigned k=0; k<n; k++) {
                checkStateI(k, iInserted[k], true);
            }
            for (unsigned k=0; k<n; k++) {
                checkStateJ(k, jInserted[k], true);
            }
        }
    }
}

/**
 * Check that the subsumption resolution works for positive instances
 *
 * L = {-p(x), q(y)}
 * M = {p(c), q(d), r(e)}
 * => Conclusion = {q(d), r(e)}
 */
TEST_FUN(PositiveSubsumptionResolution)
{
    SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION
    Kernel::Clause* L = clause({ ~p(x1), q(x1)});
    Kernel::Clause* M = clause({ p(c), q(c), r(e)});

    Kernel::Clause* L2 = clause({ p2(x1, x2), p2(f(x2), x3)});
    Kernel::Clause* M2 = clause({ ~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e)});
    // Create the expected conclusion
    Kernel::Clause* expected = clause({ q(c), r(e)});
    Kernel::Clause* expected2 = clause({ ~p2(f(y1), d), p2(g(y1), c)});
    // checks
    ASS(L);
    ASS(M);
    ASS(expected);


    SATSubsumption subsumption;

    // Check that the resolution is correct
    Kernel::Clause *conclusion = subsumption.checkSubsumptionResolution(L, M);
    ASS(conclusion)
    ASS(checkClauseEquality(conclusion, expected));
    Kernel::Clause *conclusion2 = subsumption.checkSubsumptionResolution(L2, M2);
    ASS(conclusion2)
    ASS(checkClauseEquality(conclusion2, expected2));

}

TEST_FUN(NegativeSubsumptionResolution)
{
    SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION
    // Create the the L clause
    Kernel::Clause* L1 = clause({ ~p(x1), q(x1)});
    Kernel::Clause* L2 = clause({ ~p(x1), ~q(x2)});
    Kernel::Clause* L3 = clause({ ~p(x1), r(c)});
    Kernel::Clause* L4 = clause({ ~p(x1), p2(x1, x2)});
    // Create the M clause
    Kernel::Clause* M1 = clause({ p(c), q(d), r(e)});
    // checks
    ASS(L1);
    ASS(M1);

    SATSubsumption subsumption;
    Kernel::Clause *conclusion = subsumption.checkSubsumptionResolution(L1, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L2, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L3, M1);
    ASS(!conclusion)
    conclusion = subsumption.checkSubsumptionResolution(L4, M1);
    ASS(!conclusion)
}
