/**
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <utility>
#include <ostream>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

namespace Kernel {

using namespace Lib;

class SplittingRecord;

struct UnitSpec
{
  UnitSpec() {}
  explicit UnitSpec(Unit* u) : _unit(u) {}
  bool operator==(const UnitSpec& o) const { return _unit==o._unit;}
  bool operator!=(const UnitSpec& o) const { return !(*this==o); }

  static unsigned hash(const UnitSpec& o)
  {
    ASS(!o.isEmpty());
    return Hash::hash(o._unit);
  }
  static bool equals(const UnitSpec& left, const UnitSpec& right){ return left==right; }

  bool isEmpty() const { return _unit==0; }
  bool isClause() const { ASS(!isEmpty()); return _unit->isClause(); }

  Clause* cl() const
  {
    ASS(!isEmpty());
    ASS(_unit->isClause());
    return static_cast<Clause*>(_unit);
  }
  Unit* unit() const { ASS(!isEmpty()); return _unit; }

  vstring toString() const
  {
    if(isClause()) {
	return cl()->toString();
    }
    else {
	return unit()->toString();
    }
    
  }
private:
  Unit* _unit;
};

typedef VirtualIterator<UnitSpec> UnitSpecIterator;


class InferenceStore
{
public:
  CLASS_NAME(InferenceStore);
  USE_ALLOCATOR(InferenceStore);
  
  static InferenceStore* instance();

  typedef List<int> IntList;

  struct FullInference
  {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { }

    void* operator new(size_t,unsigned premCnt)
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(UnitSpec);
      size-=sizeof(UnitSpec);

      return ALLOC_KNOWN(size,"InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(UnitSpec);
      size-=sizeof(UnitSpec);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt;
    Inference::Rule rule;
    UnitSpec premises[1];
  };

  void recordInference(UnitSpec unit, FullInference* inf);

  //void recordSplitting(SplittingRecord* srec, unsigned premCnt, UnitSpec* prems);
  void recordSplittingNameLiteral(UnitSpec us, Literal* lit);

  void recordIntroducedSymbol(Unit* u, bool func, unsigned number);

  void outputProof(ostream& out, Unit* refutation);
  void outputProof(ostream& out, UnitList* units);

  UnitSpecIterator getParents(UnitSpec us, Inference::Rule& rule);
  UnitSpecIterator getParents(UnitSpec us);

  vstring getUnitIdStr(UnitSpec cs);
  vstring getClauseIdSuffix(UnitSpec cs);

  bool findInference(UnitSpec cs, FullInference*& finf)
  {
    return _data.find(cs,finf);
  }

private:
  InferenceStore();

  struct ProofPrinter;
  struct TPTPProofPrinter;
  struct ProofCheckPrinter;

  ProofPrinter* createProofPrinter(ostream& out);

  /**
   * A map that for a clause specified by its non-prop. part
   * in Clause object and by prop. part in BDDNode yields an
   * inference that was used to derive this clause.
   *
   * If all premises of a clause have their propositional parts
   * equal to false, and it is the inference with which the
   * Clause object was created, then the inference is not stored
   * here, and the one in clause->inference() is valid.
   *
   * Also clauses with propositional parts equal to true are not
   * being inserted here, as in proofs they're derived by the
   * "tautology introduction" rule that takes no premises.
   */
  DHMap<UnitSpec, FullInference*, UnitSpec> _data;
  DHMultiset<Clause*, PtrIdentityHash> _nextClIds;

  DHMap<UnitSpec, Literal*, UnitSpec> _splittingNameLiterals;


  DHMap<Clause*, IntList*> _bddizeVars;

  /** first is true for function symbols, second is symbol number */
  typedef pair<bool,unsigned> SymbolId;
  typedef Stack<SymbolId> SymbolStack;
  DHMap<unsigned,SymbolStack> _introducedSymbols;

  //BDD* _bdd;
};


};

#endif /* __InferenceStore__ */
