/**
 * @file IndexManager.hpp
 * Defines class IndexManager
 *
 */

#ifndef __IndexManager__
#define __IndexManager__

#include "../Saturation/Forwards.hpp"
#include "../Lib/DHMap.hpp"
#include "Index.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  GENERATING_SUBST_TREE
};

class IndexManager
{
public:
  explicit IndexManager(SaturationAlgorithm* alg) : _alg(alg) {}
  Index* request(IndexType t);
  void release(IndexType t);
  bool contains(IndexType t);
private:
  struct Entry {
    Index* index;
    int refCnt;
  };
  SaturationAlgorithm* _alg;
  DHMap<IndexType,Entry> _store;
  
  Index* create(IndexType t);
};

};

#endif /*__IndexManager__*/
