/**
 * @file Storage.hpp
 * Defines class Storage.
 */

#ifndef __Storage__
#define __Storage__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/SineUtils.hpp"

namespace Shell
{
namespace LTB
{

using namespace Kernel;

struct StorageCorruptedException
: public Exception
{
  StorageCorruptedException()
  : Exception("The storage of SInE data is corrupted")
  {}
};

typedef SineSymbolExtractor::SymId SymId;
typedef SineSymbolExtractor::SymIdIterator SymIdIterator;

typedef List<string> StringList;
typedef Stack<string> StringStack;
typedef VirtualIterator<string> StringIterator;

typedef pair<unsigned, Unit*> DUnitRecord;
typedef pair<unsigned, SymId> DSymRecord;

typedef VirtualIterator<DUnitRecord> DURIterator;
typedef VirtualIterator<DSymRecord> DSRIterator;

class Storage {
public:
  Storage(bool translateSignature);
  ~Storage();

  /////////// retrieving ////////

  StringList* getTheoryFileNames();
  void getSignatureSize(int& preds, int& funs);

  VirtualIterator<pair<bool, unsigned> > getGlobalSymbols(Stack<pair<bool, unsigned> >& syms);
  void getLocalSymbols(VirtualIterator<pair<bool,unsigned> > globSyms, DHMap<pair<bool,unsigned>, unsigned>& resMap);

  SymIdIterator getDRelatedSymbols(Stack<SymId>& qsymbols, unsigned itolerance);
  VirtualIterator<unsigned> getDRelatedUnitNumbers(SymIdIterator qsymbols, unsigned itolerance);

  VirtualIterator<unsigned> getNumbersOfUnitsWithoutSymbols();

  UnitList* getClausesByUnitNumbers(VirtualIterator<unsigned> numIt);

  //////////// storing //////////
  void storeSignature();

  void storeTheoryFileNames(StringStack& fnames);

  void storeCNFOfUnit(unsigned unitNumber, ClauseIterator cit);

  void storeUnitsWithoutSymbols(Stack<Unit*>& units);

  void storeDURs(SymId s, Stack<DUnitRecord>& durs);
  void storeDSRs(SymId s, Stack<DSymRecord>& dsrs);

private:
  class StorageImpl;

  enum KeyPrefix
  {
    /** Key continues by "<name>_<arity>", value contains predicate number in the global signature */
    PRED_TO_NUM,
    /** Key continues by "<name>_<arity>", value contains function number in the global signature */
    FUN_TO_NUM,
    /** Key continues by "<number in global signature>", value contains predicate name */
    PRED_NUM_NAME,
    /** Key continues by "<number in global signature>", value contains function name */
    FUN_NUM_NAME,
    /** Key continues by "<number in global signature>", value contains predicate arity */
    PRED_NUM_ARITY,
    /** Key continues by "<number in global signature>", value contains function arity */
    FUN_NUM_ARITY,
    /** Value contains list of theory file names separated by NULL character */
    THEORY_FILES,
    /** Value contains <number of predicates><number of functions> */
    PRED_FUN_CNT,
    /** Key continues by "<number of unit>", value contains the unit converted to the CNF form
     * (See @b storeCNFOfUnit for details) */
    UNIT_CNF,
    /** Value contains sequence of numbers of units without symbols */
    UNITS_WITHOUT_SYMBOLS,
    /** Key continues by "<SymId>", value contains numbers of units D-related with the symbol
     * (See @b storeDURs for details) */
    SYM_DURS,
    /** Key continues by "<SymId>", value contains SymIds D-related with the symbol
     * (See @b storeDSRs for details) */
    SYM_DSRS,
    /** Equal to number of different prefixes */
    PREFIX_COUNT
  };

  string getConstKey(KeyPrefix p);
  string getIntKey(KeyPrefix p, int keyNum);

  StringIterator getIntKeyValues(KeyPrefix p, VirtualIterator<int> keyNums);

  void storeConstKey(KeyPrefix p, char* val, size_t valLen);
  void storeIntKey(KeyPrefix p, int keyNum, char* val, size_t valLen);

  void storeSymbolInfo(Signature::Symbol* sym, int index, bool function);

  static const unsigned storedIntMaxSize=4;
  static size_t dumpInt(int num, char* bufStart);
  size_t readInt(const char* buf, int& num);


  DHMap<pair<bool, unsigned>, unsigned> _glob2loc;
  bool _translateSignature;
  StorageImpl* _impl;
};

}
}

#endif // __Storage__
