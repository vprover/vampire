/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Saturation_LapPE__
#define __Saturation_LapPE__

#include <vector>
#include <utility>
#include <numeric>
#include <algorithm>

#include <Eigen/Dense>
#include <Eigen/Sparse>
#include <Spectra/SymEigsSolver.h>
#include <Spectra/MatOp/SparseSymMatProd.h>

#include "Lib/Random.hpp"

/**
 * Compute Laplacian Eigenvector Positional Encoding (LapPE) for a bipartite
 * symbol-clause incidence graph.
 *
 * The bipartite graph has numSymbols + numClauses nodes. Symbols are indexed
 * 0..numSymbols-1, clauses numSymbols..N-1. An edge (s, c) means symbol s
 * occurs in clause c.
 *
 * We compute the normalized Laplacian L_sym = I - D^{-1/2} A D^{-1/2}.
 * Since L_sym and A_norm = D^{-1/2} A D^{-1/2} share eigenvectors,
 * we find the largest eigenvalues of A_norm (which correspond to the
 * smallest eigenvalues of L_sym) using a standard eigensolver,
 * avoiding the singularity issue with shift-and-invert on L.
 *
 * Returns two flat row-major vectors: symbolPE (numSymbols * k) and
 * clausePE (numClauses * k), ready for torch::from_blob.
 */
inline std::pair<std::vector<float>, std::vector<float>> computeLapPE(
    unsigned numSymbols,
    unsigned numClauses,
    const std::vector<std::pair<unsigned, unsigned>>& incidenceEdges,
    unsigned k = 8)
{
  unsigned N = numSymbols + numClauses;

  // Edge case: trivial graph
  if (N <= 1 || incidenceEdges.empty()) {
    return {std::vector<float>(numSymbols * k, 0.0f),
            std::vector<float>(numClauses * k, 0.0f)};
  }

  // 1. Compute degree of each node
  Eigen::VectorXf deg = Eigen::VectorXf::Zero(N);
  for (auto& [s, c] : incidenceEdges) {
    unsigned ci = numSymbols + c;
    deg(s) += 1.0f;
    deg(ci) += 1.0f;
  }

  Eigen::VectorXf deg_inv_sqrt(N);
  for (unsigned i = 0; i < N; i++) {
    deg_inv_sqrt(i) = (deg(i) > 0.0f) ? (1.0f / std::sqrt(deg(i))) : 0.0f;
  }

  // 2. Build normalized adjacency A_norm = D^{-1/2} A D^{-1/2} as sparse matrix
  std::vector<Eigen::Triplet<float>> triplets;
  triplets.reserve(incidenceEdges.size() * 2);
  for (auto& [s, c] : incidenceEdges) {
    unsigned ci = numSymbols + c;
    float val = deg_inv_sqrt(s) * deg_inv_sqrt(ci);
    triplets.emplace_back(s, ci, val);
    triplets.emplace_back(ci, s, val);
  }

  Eigen::SparseMatrix<float> A_norm(N, N);
  A_norm.setFromTriplets(triplets.begin(), triplets.end());

  // 3. Eigendecomposition
  // The eigenvectors of A_norm are the same as those of L_sym = I - A_norm.
  // The largest eigenvalues of A_norm correspond to the smallest of L_sym.
  // We need k+1 largest eigenvalues of A_norm (to skip the trivial one).
  unsigned numEigsNeeded = std::min(k + 1, N);
  Eigen::MatrixXf eigVecs; // will hold eigenvectors sorted by ascending L_sym eigenvalue

  static const unsigned SPARSE_THRESHOLD = 100;

  if (N < SPARSE_THRESHOLD) {
    // Dense path: use Eigen's SelfAdjointEigenSolver on the Laplacian directly
    Eigen::MatrixXf A_dense(A_norm);
    Eigen::MatrixXf L_dense = Eigen::MatrixXf::Identity(N, N) - A_dense;
    Eigen::SelfAdjointEigenSolver<Eigen::MatrixXf> solver(L_dense);
    if (solver.info() != Eigen::Success) {
      return {std::vector<float>(numSymbols * k, 0.0f),
              std::vector<float>(numClauses * k, 0.0f)};
    }
    // Eigenvalues are in ascending order by default -- exactly what we want
    eigVecs = solver.eigenvectors();
  } else {
    // Sparse path: find k+1 largest eigenvalues of A_norm using SymEigsSolver
    unsigned ncv = std::min(2 * numEigsNeeded + 1, N);

    Spectra::SparseSymMatProd<float> op(A_norm);
    Spectra::SymEigsSolver<Spectra::SparseSymMatProd<float>> solver(op, numEigsNeeded, ncv);
    solver.init();
    solver.compute(Spectra::SortRule::LargestAlge, 1000, 1e-6f);

    if (solver.info() != Spectra::CompInfo::Successful) {
      // Fallback: try dense if not too large, otherwise return zeros
      if (N < 5000) {
        Eigen::MatrixXf A_dense(A_norm);
        Eigen::MatrixXf L_dense = Eigen::MatrixXf::Identity(N, N) - A_dense;
        Eigen::SelfAdjointEigenSolver<Eigen::MatrixXf> dSolver(L_dense);
        if (dSolver.info() != Eigen::Success) {
          return {std::vector<float>(numSymbols * k, 0.0f),
                  std::vector<float>(numClauses * k, 0.0f)};
        }
        eigVecs = dSolver.eigenvectors();
      } else {
        return {std::vector<float>(numSymbols * k, 0.0f),
                std::vector<float>(numClauses * k, 0.0f)};
      }
    } else {
      // Spectra returns eigenvalues of A_norm in descending order (LargestAlge).
      // L_sym eigenvalue = 1 - A_norm eigenvalue.
      // So the largest A_norm eigenvalue -> smallest L_sym eigenvalue.
      // We need ascending L_sym order, which is descending A_norm order = as returned.
      Eigen::VectorXf aEvals = solver.eigenvalues();  // descending
      Eigen::MatrixXf evecs = solver.eigenvectors();

      // Columns are already in order: first column = largest A_norm eval = smallest L_sym eval (trivial).
      // We just use them directly.
      eigVecs = evecs;
    }
  }

  // 4. Extract PE: skip first eigenvector (trivial), take next k
  unsigned availableEigVecs = eigVecs.cols();
  unsigned startCol = 1; // skip trivial eigenvector
  unsigned numPECols = std::min(k, (availableEigVecs > 1) ? (availableEigVecs - 1) : 0u);

  // 5. Build output vectors (row-major: node0_feat0, node0_feat1, ..., node1_feat0, ...)
  std::vector<float> symbolPE(numSymbols * k, 0.0f);
  std::vector<float> clausePE(numClauses * k, 0.0f);

  for (unsigned col = 0; col < numPECols; col++) {
    // Random sign flip
    float sign = Lib::Random::getBit() ? 1.0f : -1.0f;

    for (unsigned i = 0; i < numSymbols; i++) {
      symbolPE[i * k + col] = sign * eigVecs(i, startCol + col);
    }
    for (unsigned i = 0; i < numClauses; i++) {
      clausePE[i * k + col] = sign * eigVecs(numSymbols + i, startCol + col);
    }
  }
  // Remaining columns (if numPECols < k) are already zero-initialized

  return {std::move(symbolPE), std::move(clausePE)};
}

#endif // __Saturation_LapPE__
