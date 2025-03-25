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
 * @file IndexManager.hpp
 * Defines class IndexManager
 *
 */

#ifndef __IndexManager__
#define __IndexManager__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Index.hpp"

#include "Lib/Allocator.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"


namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  BINARY_RESOLUTION_SUBST_TREE=1,
  BACKWARD_SUBSUMPTION_SUBST_TREE,
  FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE,

  URR_UNIT_CLAUSE_SUBST_TREE,
  URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE,
  
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,
  SUB_VAR_SUP_SUBTERM_SUBST_TREE,
  SUB_VAR_SUP_LHS_SUBST_TREE,
  ALASCA_FOURIER_MOTZKIN_LHS_SUBST_TREE,
  ALASCA_FOURIER_MOTZKIN_RHS_SUBST_TREE,
  ALASCA_BINARY_RESOLUTION_LHS_SUBST_TREE,
  ALASCA_BINARY_RESOLUTION_RHS_SUBST_TREE,
  ALASCA_SUPERPOSITION_LHS_SUBST_TREE,
  ALASCA_SUPERPOSITION_RHS_SUBST_TREE,
  ALASCA_COHERENCE_RHS_SUBST_TREE,
  ALASCA_COHERENCE_LHS_SUBST_TREE,
  ALASCA_FWD_DEMODULATION_SUBST_TREE,
  ALASCA_BWD_DEMODULATION_SUBST_TREE,

  DEMODULATION_SUBTERM_SUBST_TREE,
  DEMODULATION_LHS_CODE_TREE,

  FW_SUBSUMPTION_CODE_TREE,
  FW_SUBSUMPTION_SUBST_TREE,
  BW_SUBSUMPTION_SUBST_TREE,

  FSD_SUBST_TREE,

  REWRITE_RULE_SUBST_TREE,

  ACYCLICITY_INDEX,
  NARROWING_INDEX,
  PRIMITIVE_INSTANTIATION_INDEX,
  SKOLEMISING_FORMULA_INDEX,
  RENAMING_FORMULA_INDEX,

  UNIT_INT_COMPARISON_INDEX,
  INDUCTION_TERM_INDEX,
  STRUCT_INDUCTION_TERM_INDEX,
};

class IndexManager
{
public:
  /** alg can be zero, then it must be set by setSaturationAlgorithm */
  explicit IndexManager(SaturationAlgorithm* alg);
  void setSaturationAlgorithm(SaturationAlgorithm* alg) 
  { 
    ASS(!_alg);
    ASS(alg);
    _alg = alg; 
  }
  Index* request(IndexType t);
  void release(IndexType t);
  bool contains(IndexType t);
  Index* get(IndexType t);

  void provideIndex(IndexType t, Index* index);
private:

  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm* _alg;
  DHMap<IndexType,Entry> _store;

  Index* create(IndexType t);
  Shell::Options::UnificationWithAbstraction _uwa;
  bool _uwaFixedPointIteration;
};

};

#endif /*__IndexManager__*/
