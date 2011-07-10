/**
 * @file Sorts.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include <string>

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"

namespace Kernel {

class Sorts {
public:
  /** The default sort that is to be used when no sort is declared */
  static const unsigned SRT_DEFAULT;
  static const unsigned SRT_BOOL;
  static const unsigned SRT_INTEGER;
  static const unsigned SRT_RATIONAL;
  static const unsigned SRT_REAL;
  static const unsigned FIRST_USER_SORT;

  Sorts();
  ~Sorts();

  enum SortKind
  {
    ATOMIC,
    PRODUCT,
    ARROW,
  };

  class SortInfo
  {
  public:
    SortInfo(SortKind kind, const string& name) : _kind(kind), _name(name) {}

    const string& name() const { return _name; }
    SortKind kind() const { return _kind; }
  private:
    SortKind _kind;
    string _name;
  };

  class ProductSortInfo : public SortInfo
  {
  public:
    ProductSortInfo(const string& name, unsigned arity, unsigned* children)
    : SortInfo(PRODUCT, name)
    {
      _children.initFromArray(arity, children);
    }
    const DArray<unsigned>& children() const { return _children; }
  private:
    DArray<unsigned> _children;
  };

  class ArrowSortInfo : public SortInfo
  {
  public:
    ArrowSortInfo(const string& name, unsigned leftSort, unsigned rightSort)
    : SortInfo(PRODUCT, name), _left(leftSort), _right(rightSort) {}

    unsigned left() const { return _left; }
    unsigned right() const { return _right; }
  private:
    unsigned _left;
    unsigned _right;
  };

  unsigned addSort(const string& name, bool& added);
  unsigned addSort(const string& name);
  unsigned addProductSort(const string& name, unsigned arity, unsigned* children, bool& added);
  unsigned addArrowSort(const string& name, unsigned leftSort, unsigned rightSort, bool& added);

  const string& sortName(unsigned idx) const
  {
    CALL("Sorts::sortName");
    return _sorts[idx]->name();
  }

  /**
   * Return the number of sorts
   */
  unsigned sorts() const { return _sorts.length(); }

  const SortInfo* getSortInfo(unsigned sort) const { return _sorts[sort]; }

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

  unsigned arity() const { return _args ? _args->length() : 0; }
  virtual bool isAllDefault() const;

  virtual bool isFunctionType() const { return false; }

  bool operator==(const BaseType& o) const;
  bool operator!=(const BaseType& o) const { return !(*this==o); }
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

  virtual bool isAllDefault() const;
  virtual bool isFunctionType() const { return true; }
private:
  unsigned _result;
};

}

#endif // __Sorts__
