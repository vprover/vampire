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

#include "Lib/ConstTypeId.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {

  URR_UNIT_CLAUSE_SUBST_TREE,
  URR_UNIT_CLAUSE_WITH_AL_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_SUBST_TREE,
  URR_NON_UNIT_CLAUSE_WITH_AL_SUBST_TREE,
  
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,
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

  BW_SUBSUMPTION_SUBST_TREE,

  REWRITE_RULE_SUBST_TREE,

  ACYCLICITY_INDEX,
  SKOLEMISING_FORMULA_INDEX,

  INDUCTION_TERM_INDEX,
  STRUCT_INDUCTION_TERM_INDEX,
};

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm& alg);

  template<typename IndexType, bool isGenerating>
  constexpr static auto key()
  { return std::make_pair(ConstTypeId::getTypeId<IndexType>(), isGenerating); }

  template<typename IndexType, bool isGenerating>
  IndexType* request()
  {
    Entry* e;
    if (_store2.getValuePtr(key<IndexType, isGenerating>(), e)) {
      e->index = new IndexType();
      attachContainer<isGenerating>(e->index);
      e->refCnt=1;
    } else {
      e->refCnt++;
    }
    return static_cast<IndexType*>(e->index);
  }
  Index* request(IndexType t);

  template<typename IndexType, bool isGenerating>
  void release()
  {
    auto ptr = _store2.findPtr(key<IndexType, isGenerating>());
    ASS(ptr);

    ptr->refCnt--;
    if (ptr->refCnt == 0) {
      delete ptr->index;
      _store2.remove(key<IndexType, isGenerating>());
    }
  }
  void release(IndexType t);

  template<typename IndexType, bool isGenerating>
  bool contains()
  {
    return _store2.find(key<IndexType, isGenerating>());
  }
  bool contains(IndexType t);

  template<typename IndexType, bool isGenerating> IndexType* get()
  {
    return static_cast<IndexType*>(_store2.get(key<IndexType, isGenerating>()).index);
  }
  Index* get(IndexType t);

private:
  Index* create(IndexType t);
  template<bool isGenerating>
  void attachContainer(Index* i);

  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm& _alg;
  DHMap<IndexType,Entry> _store;
  DHMap<std::pair<ConstTypeId,bool>,Entry> _store2;
};

};

#endif /*__IndexManager__*/
