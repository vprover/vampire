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

//TODO: make generating and symplifying subst. trees different, when needed
enum IndexType {
  GENERATING_SUBST_TREE = 1,
  SIMPLIFYING_SUBST_TREE = 1
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
