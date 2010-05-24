/**
 * @file Storage.hpp
 * Defines class Storage.
 */

#ifndef __Storage__
#define __Storage__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"

#include "Lib/List.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Signature.hpp"

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

typedef List<string> StringList;
typedef Stack<string> StringStack;

class Storage {
public:
  Storage(bool translateSignature);
  ~Storage();

  void dumpSignature();
  void storeTheoryFileNames(StringStack& fnames);
  StringList* getTheoryFileNames();

private:

  void storeSymbolInfo(Signature::Symbol* sym, int index, bool function);

  static const int storedIntMaxSize=4;
  static size_t storeInt(int num, char* bufStart);

  class StorageImpl;

  enum KeyPrefix
  {
    /** Key continues by "<name>/<arity>", value contains predicate number in the global signature */
    PRED_TO_NUM,
    /** Key continues by "<name>/<arity>", value contains function number in the global signature */
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
    /** Equal to number of different prefixes */
    PREFIX_COUNT
  };

  bool _translateSignature;
  StorageImpl* _impl;
};

}
}

#endif // __Storage__
