/**
 * @file IndexManager.hpp
 * Defines class IndexManager
 *
 */

#ifndef __IndexManager__
#define __IndexManager__

#include "../Forwards.hpp"
#include "../Lib/DHMap.hpp"
#include "Index.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  GENERATING_SUBST_TREE=1,
  SIMPLIFYING_SUBST_TREE,
  SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE,
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,
  DEMODULATION_SUBTERM_SUBST_TREE,
  DEMODULATION_LHS_SUBST_TREE,

  FW_SUBSUMPTION_CODE_TREE,

  FW_SUBSUMPTION_SUBST_TREE,
  BW_SUBSUMPTION_SUBST_TREE,

  REWRITE_RULE_SUBST_TREE,
  ARITHMETIC_INDEX
};

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm* alg) : _alg(alg), _genLitIndex(0) {}
  Index* request(IndexType t);
  void release(IndexType t);
  bool contains(IndexType t);

  LiteralIndexingStructure* getGeneratingLiteralIndexingStructure() { return _genLitIndex; };
private:
  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm* _alg;
  DHMap<IndexType,Entry> _store;

  LiteralIndexingStructure* _genLitIndex;

  Index* create(IndexType t);
};

};

#endif /*__IndexManager__*/
