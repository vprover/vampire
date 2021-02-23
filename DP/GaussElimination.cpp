/*
 * File GaussElimination.cpp.
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
 * @file GaussElimination.cpp
 * Implements class GaussElimination.
 */

#define DLADP 1

#include "GaussElimination.hpp"

//#include "Kernel/Rational.hpp"
#include "Lib/List.hpp"

#include <iostream>
#include <vector>
#include <iterator>
#include <set>
#include <typeinfo>

//#include "Lib/Environment.hpp"

namespace DP {

template <typename T>
inline bool isAllZero(std::vector<T> v, int startIndex, int endIndexExclusive)
{
    for (int i = startIndex; i < endIndexExclusive; i++)
    {
        if (v[i] != 0)
            return false;
    }
    return true;
}

template <typename T>
inline bool isAllZero(const T array[], int startIndex, int endIndexExclusive)
{
    for (int i = startIndex; i < endIndexExclusive; i++)
    {
        if (array[i] != 0)
            return false;
    }
    return true;
}

template <typename T>
void printVector(std::vector<T> v)
{
    for (auto i = v.begin(); i != v.end(); ++i)
    {
        std::cout << *i << ' ';
    }

    std::cout << std::endl;
}

template <typename T>
void printArray(const T array[], int startIndex, int endIndexExclusive)
{
    for (int i = startIndex; i < endIndexExclusive; i++)
    {
        std::cout << array[i] << ' ';
    }

    std::cout << std::endl;
}


GaussElimination::GaussElimination(float **augmentedMatrix, int numberOfUnkowns, int numberOfEquations)
{
    //CALL("GaussElimination::GaussElimination");
    this->augmentedMatrix = augmentedMatrix;
    this->numberOfUnkowns = numberOfUnkowns;
    this->numberOfEquations = numberOfEquations;
}

void GaussElimination::solve()
{
    //CALL("GaussElimination::solve");
    // List holding the labels of the unkonws
    int colLabelList[numberOfUnkowns];
    for (int i = 0; i < numberOfUnkowns; i++)
    {
        colLabelList[i] = i;
    }

    float **newRowList = new float *[numberOfEquations];
    int newRowListNextIndex = 0;
    std::set<int> rowsLeftIndex;
    for (size_t i = 0; i < numberOfEquations; i++)
    {
        rowsLeftIndex.insert(i);
    }

    for (size_t i = 0; i < numberOfUnkowns; i++)
    {
        int colLabel = colLabelList[i];

        std::vector<size_t> rowsIndexWithNonZero;
        for (auto &rowIndex : rowsLeftIndex)
        {
            if (augmentedMatrix[rowIndex][colLabel] != 0)
            {
                rowsIndexWithNonZero.emplace_back(rowIndex);
            }
        }

        if (rowsIndexWithNonZero.size() != 0)
        {
            size_t pivotIndex = rowsIndexWithNonZero[0];
            rowsLeftIndex.erase(pivotIndex);
            newRowList[newRowListNextIndex] = augmentedMatrix[pivotIndex];
            newRowListNextIndex++;

            for (size_t j = 1; j < rowsIndexWithNonZero.size(); j++)
            {
                int rowIndex = rowsIndexWithNonZero[j];
                float multiplier = augmentedMatrix[rowIndex][colLabel] / augmentedMatrix[pivotIndex][colLabel];
                std::cout << "Multiplier:" << multiplier << std::endl;
                for (size_t k = i; k < numberOfUnkowns; k++)
                {
                    int colLabel = colLabelList[k];
                    augmentedMatrix[rowIndex][colLabel] -= multiplier * augmentedMatrix[pivotIndex][colLabel];
                }

                augmentedMatrix[rowIndex][numberOfUnkowns] -= multiplier * augmentedMatrix[pivotIndex][numberOfUnkowns];
            }
        }
    }

    for (auto &rowIndex : rowsLeftIndex)
    {
        newRowList[newRowListNextIndex++] = augmentedMatrix[rowIndex];
    }

    for (int i = 0; i < numberOfEquations; i++)
    {
        printArray(newRowList[i], 0, numberOfUnkowns + 1);
    }

    std::cout << "\n********************\n"
              << std::endl;

    // Checking satifiability
    for (int i = numberOfEquations - 1; i >= 0; i--)
    {
        float *row = newRowList[i];
        bool cofficientOfRowAreZero = isAllZero(row, 0, numberOfUnkowns);
        if (cofficientOfRowAreZero && row[numberOfUnkowns])
        {
            std::cout << "Unsatisfiable: ";
            printArray(row, 0, numberOfUnkowns + 1);
            return;
        }
    }

    // At this point satisfiable. Possibly infinite solutions
    // if matrix is triangular form use back subsitution
    if (numberOfEquations < numberOfUnkowns)
    {
        std::cout << "Satisfiable1: Infinite Solutions" << std::endl;
        return;
    }

    for (int i = 0; i < numberOfUnkowns; i++)
    {
        if (newRowList[i][i] == 0)
        {
            std::cout << "Satisfiable2: Infinite Solutions" << std::endl;
            return;
        }
    }

    // At this point, matrix in triangular form
    int solution[numberOfUnkowns];
    solution[numberOfUnkowns - 1] = newRowList[numberOfUnkowns - 1][numberOfUnkowns] / newRowList[numberOfUnkowns - 1][numberOfUnkowns - 1];

    for (int i = numberOfUnkowns - 2; i >= 0; i--)
    {
        solution[i] = newRowList[i][numberOfUnkowns];

        for (int j = i + 1; j < numberOfUnkowns; j++)
        {
            solution[i] = solution[i] - newRowList[i][j] * solution[j];
        }

        solution[i] = solution[i] / newRowList[i][i];
    }
    delete[] newRowList;
    printArray(solution, 0, numberOfUnkowns);
}

}

#if GAUSS 

int main()
{
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

    return 0;
}
#endif

