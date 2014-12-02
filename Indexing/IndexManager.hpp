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

#include "Saturation/SaturationAlgorithmContext.hpp"

#include "Lib/Allocator.hpp"

namespace Saturation{
  class SaturationAlgorithm;
}

namespace Indexing
{

using namespace Lib;
using namespace Saturation;

enum IndexType {
  GENERATING_SUBST_TREE=1,
  SIMPLIFYING_SUBST_TREE,
  SIMPLIFYING_UNIT_CLAUSE_SUBST_TREE,
  GENERATING_UNIT_CLAUSE_SUBST_TREE,
  GENERATING_NON_UNIT_CLAUSE_SUBST_TREE,
  SUPERPOSITION_SUBTERM_SUBST_TREE,
  SUPERPOSITION_LHS_SUBST_TREE,
  DEMODULATION_SUBTERM_SUBST_TREE,
  DEMODULATION_LHS_SUBST_TREE,

  FW_SUBSUMPTION_CODE_TREE,

  FW_SUBSUMPTION_SUBST_TREE,
  BW_SUBSUMPTION_SUBST_TREE,

  REWRITE_RULE_SUBST_TREE,

  GLOBAL_SUBSUMPTION_INDEX,
//  ARITHMETIC_INDEX
};

class IndexManager
{
public:
  CLASS_NAME(IndexManager);
  USE_ALLOCATOR(IndexManager);

  /** alg can be zero, then it must be set by setSaturationAlgorithm */
 // explicit IndexManager(SaturationAlgorithm* alg);
  explicit IndexManager(): _genLitIndex(0) {}
  ~IndexManager() {}
  //void setSaturationAlgorithm(SaturationAlgorithm* alg);
  Index* request(IndexType t);
  void release(IndexType t);
  bool contains(IndexType t);
  Index* get(IndexType t);

  void provideIndex(IndexType t, Index* index);

  LiteralIndexingStructure* getGeneratingLiteralIndexingStructure() { ASS(_genLitIndex); return _genLitIndex; };

private:

  static bool isLocalIndex(IndexType t){
    switch(t){
      //case BW_SUBSUMPTION_SUBST_TREE:
      // list other global indexes here
      //  return false;

      default: return true;
    }
  }

  //void attach(SaturationAlgorithm* salg);

  struct Entry {
    Index* index;
    int refCnt;
    bool local;
  };

  //SaturationAlgorithm* _alg;

  bool getEntry(IndexType t,Entry& e){
    if(!_globalStore.find(t,e)){
      SaturationAlgorithmContext* ctx = static_cast<SaturationAlgorithmContext*> (MainLoopContext::currentContext);
      auto p = pair<SaturationAlgorithmContext*,IndexType>(ctx,t);
      return _localStore.find(p,e);
    }
    else return true;
  }
  void putEntry(IndexType t,Entry& e){
    if(e.local){
      SaturationAlgorithmContext* ctx = static_cast<SaturationAlgorithmContext*> (MainLoopContext::currentContext);
      auto p = pair<SaturationAlgorithmContext*,IndexType>(ctx,t);
       _localStore.insert(p,e);
    }
    else _globalStore.insert(t,e);
  }

  void removeFromStore(IndexType t, Entry e){
    if(e.local){
      SaturationAlgorithmContext* ctx = static_cast<SaturationAlgorithmContext*> (MainLoopContext::currentContext);
      auto p = pair<SaturationAlgorithmContext*,IndexType>(ctx,t);
       _localStore.remove(p);
    }
    else _globalStore.remove(t);
  }


  //TODO - replace with Entry* ?
  DHMap<IndexType,Entry> _globalStore;
  DHMap<pair<SaturationAlgorithmContext*,IndexType>,Entry> _localStore;

  LiteralIndexingStructure* _genLitIndex;

  Index* create(IndexType t);
};

};

#endif /*__IndexManager__*/
