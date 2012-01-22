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
  /** The default sort that is to be used when no sort is declared */
  enum DefaultSorts {
    SRT_DEFAULT = 0,
    SRT_BOOL = 1,
    SRT_INTEGER = 2,
    SRT_RATIONAL = 3,
    SRT_REAL = 4,
    FIRST_USER_SORT = 5
  };

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

  bool haveSort(const string& name);
  bool findSort(const string& name, unsigned& idx);

  const string& sortName(unsigned idx) const
  {
    CALL("Sorts::sortName");
    return _sorts[idx]->name();
  }

  /**
   * Return the number of sorts
   */
  unsigned sorts() const { return _sorts.length(); }
  /** true if there is a sort different from built-ins */
  bool hasSort() const {return _hasSort;}

private:
  SymbolMap _sortNames;
  Stack<SortInfo*> _sorts;
  /** true if there is a sort different from built-ins */
  bool _hasSort;
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

  unsigned arity() const { return _args ? _args->length() : 0; }
  virtual bool isAllDefault() const;

  virtual bool isFunctionType() const { return false; }

  bool operator==(const BaseType& o) const;
  bool operator!=(const BaseType& o) const { return !(*this==o); }

  virtual string toString() const = 0;

  static BaseType* makeType(unsigned arity, const unsigned* domainSorts, unsigned rangeSort);
  static BaseType* makeType0(unsigned rangeSort);
  static BaseType* makeType1(unsigned arg1Sort, unsigned rangeSort);
  static BaseType* makeType2(unsigned arg1Sort, unsigned arg2Sort, unsigned rangeSort);
  static BaseType* makeType3(unsigned arg1Sort, unsigned arg2Sort, unsigned arg3Sort, unsigned rangeSort);
protected:
  BaseType(unsigned arity, const unsigned* sorts=0);

  string argsToString() const;
private:
  typedef Vector<unsigned> SortVector;
  SortVector* _args;
};

class PredicateType : public BaseType
{
public:
  PredicateType(unsigned arity, const unsigned* argumentSorts = 0)
   : BaseType(arity, argumentSorts) {}

  virtual string toString() const;
};

class FunctionType : public BaseType
{
public:
  FunctionType(unsigned arity, const unsigned* argumentSorts, unsigned resultSort)
   : BaseType(arity, argumentSorts), _result(resultSort) {}
  FunctionType(unsigned arity);

  unsigned result() const { return _result; }

  virtual bool isAllDefault() const;
  virtual bool isFunctionType() const { return true; }

  virtual string toString() const;
private:
  unsigned _result;
};

}

#endif // __Sorts__
