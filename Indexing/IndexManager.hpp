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
#include "Kernel/MismatchHandler.hpp"

#include "Lib/Allocator.hpp"
#include "Kernel/MismatchHandler.hpp"


namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  BINARY_RESOLUTION_SUBST_TREE=1,
  BACKWARD_SUBSUMPTION_SUBST_TREE,
  FW_SUBSUMPTION_UNIT_CLAUSE_SUBST_TREE,

  URR_UNIT_CLAUSE_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_SUBST_TREE,
  
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,

  DEMODULATION_SUBTERM_SUBST_TREE,
  DEMODULATION_LHS_CODE_TREE,
  DEMODULATION_LHS_SUBST_TREE,

  FW_SUBSUMPTION_SUBST_TREE,
  BW_SUBSUMPTION_SUBST_TREE,

  FSD_SUBST_TREE,

  REWRITE_RULE_SUBST_TREE,

  GLOBAL_SUBSUMPTION_INDEX,

  ACYCLICITY_INDEX,

#if VHOL
  SKOLEMISING_FORMULA_INDEX,
#endif

  UNIT_INT_COMPARISON_INDEX,
  INDUCTION_TERM_INDEX,
  STRUCT_INDUCTION_TERM_INDEX,
};

class IndexManager
{
public:
  CLASS_NAME(IndexManager);
  USE_ALLOCATOR(IndexManager);

  /** alg can be zero, then it must be set by setSaturationAlgorithm */
  explicit IndexManager(SaturationAlgorithm* alg);

  void setSaturationAlgorithm(SaturationAlgorithm* alg) 
  { 
    CALL("IndexManager::setSaturationAlgorithm");
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
