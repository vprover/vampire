/**
 * @file Sorts.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include <string>

#include "Forwards.hpp"

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"

namespace Kernel {

class Sorts {
public:
  Sorts();
  ~Sorts();

  class SortInfo
  {
  public:
    SortInfo(const string& name) : _name(name) {}

    const string& name() const { return _name; }
  private:
    string _name;
  };

  unsigned addSort(const string& name, bool& added);
  unsigned addSort(const string& name);

  const string& sortName(unsigned idx) const
  {
    CALL("Sorts::sortName");
    return _sorts[idx]->name();
  }

  /**
   * The default sort that is to be used when no sort is declared
   */
  unsigned defaultSort() const
  { return 0; }
private:
  SymbolMap _sortNames;
  Stack<SortInfo*> _sorts;
};

class BaseType
{
public:
  virtual ~BaseType();

  unsigned arg(unsigned idx) const
  {
    CALL("PredicateType::arg");
    return (*_args)[idx];
  }
protected:
  BaseType(unsigned arity, unsigned* sorts=0);
private:
  typedef Vector<unsigned> SortVector;
  SortVector* _args;
};

class PredicateType : public BaseType
{
public:
  PredicateType(unsigned arity, unsigned* argumentSorts = 0)
   : BaseType(arity, argumentSorts) {}
};

class FunctionType : public BaseType
{
public:
  FunctionType(unsigned arity, unsigned* argumentSorts, unsigned resultSort)
   : BaseType(arity, argumentSorts), _result(resultSort) {}
  FunctionType(unsigned arity);

  unsigned result() const { return _result; }
private:
  unsigned _result;
};

}

#endif // __Sorts__
