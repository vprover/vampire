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
#include "DP/GaussElimination.hpp"

#define UNIT_ID GaussElim
UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"

void test_eliminate() {
    int numberOfEquation = 2;
    int numberOfUnkowns = 2;
    //Rational::Rational test = Rational(3);

    float **rowlist = new float *[numberOfEquation];
    for (int i = 0; i < numberOfEquation; i++)
        rowlist[i] = new float[numberOfUnkowns + 1];

    std::vector<std::vector<float>> rowVector = {{4, 3, 8}, {4, 1, 7}};

    for (int i = 0; i < numberOfEquation; i++)
        for (int j = 0; j < numberOfUnkowns + 1; j++)
            rowlist[i][j] = rowVector[i][j];

    DP::GaussElimination ge = DP::GaussElimination(rowlist, numberOfUnkowns, numberOfEquation);
    ge.solve();

    // Freeing
    for (int i = 0; i < numberOfEquation; ++i)
        delete[] rowlist[i];
    delete[] rowlist;

}

TEST_FUN(test_1){
  test_eliminate();
}
