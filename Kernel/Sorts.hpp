/**
 * @file Sorts.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include "Forwards.hpp"

#include "Lib/Map.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"

namespace Kernel {

class Sorts {
public:
  CLASS_NAME(Sorts);
  USE_ALLOCATOR(Sorts);

  /** Various pre-defined sort */
  // Note that this is not closed, these will be treated as unsigned ints within the code
  enum DefaultSorts {
    /** The default sort of all individuals, always in the non-sorted case */
    SRT_DEFAULT = 0,
    /** Boolean sort */
    SRT_BOOL = 1,
    /** sort of integers */
    SRT_INTEGER = 2,
    /** sort of rationals */
    SRT_RATIONAL = 3,
    /** sort of reals */
    SRT_REAL = 4,
    /** FOOL boolean sort */
    SRT_FOOL_BOOL = 5,
    /** this is not a sort, it is just used to denote the first index of a user-define sort */
    FIRST_USER_SORT = 6
  };

  /** Various structured sorts */
  enum class StructuredSort {
    /** The structured sort for arrays **/
    ARRAY,
    /** The structured sort for lists, currently unused **/
    LIST
  };

  Sorts();
  ~Sorts();

  class SortInfo
  {
  public:
    CLASS_NAME(SortInfo);
    USE_ALLOCATOR(SortInfo);
  
    SortInfo(const vstring& name,const unsigned id) : _name(name), _id(id) {}
    virtual ~SortInfo() {}
    
    const vstring& name() const { return _name; }
    const unsigned id() const { return _id; }

    virtual bool hasStructuredSort(StructuredSort sort) { return false; }
  protected:
    vstring _name;
    unsigned _id;
  };

  /**
   *
   * @author Giles
   */
  class StructuredSortInfo : public SortInfo
  {
  public:
    CLASS_NAME(StructuredSortInfo);
    USE_ALLOCATOR(StructuredSortInfo);

    StructuredSortInfo(vstring name, StructuredSort sort,unsigned id): 
      SortInfo(name,id), _sort(sort){}

  private:
    StructuredSort _sort;
  };

  /**
   *
   * @author Giles
   */
  class ArraySort : public StructuredSortInfo
  {
  public:
    CLASS_NAME(ArraySort);
    USE_ALLOCATOR(ArraySort);

    ArraySort(vstring name, unsigned indexSort, unsigned innerSort,unsigned id) : 
      StructuredSortInfo(name,StructuredSort::ARRAY, id), 
      _indexSort(indexSort), _innerSort(innerSort)
    { 
#if VDEBUG
      cout << "Creating ArraySort " << name << " with id " << id << endl; 
#endif
    }

    bool hasStructuredSort(StructuredSort sort) override { 
      return sort==StructuredSort::ARRAY; 
    }
    unsigned getIndexSort(){ return _indexSort; }
    unsigned getInnerSort(){ return _innerSort; }

  private:
    // the SortInfo can be found using Sorts
    unsigned _indexSort;
    unsigned _innerSort;

  };

  unsigned addSort(const vstring& name, bool& added);
  unsigned addSort(const vstring& name);

  unsigned addArraySort(unsigned indexSort, unsigned innerSort);
  VirtualIterator<unsigned> getArraySorts();
  ArraySort* getArraySort(unsigned sort){
    ASS(hasStructuredSort(sort,StructuredSort::ARRAY));
    return static_cast<ArraySort*>(_sorts[sort]);
  }

  bool haveSort(const vstring& name);
  bool findSort(const vstring& name, unsigned& idx);

  bool hasStructuredSort(unsigned sort, StructuredSort structured){
    if(sort > _sorts.size()) return false;
    return _sorts[sort]->hasStructuredSort(structured);
  }

  const vstring& sortName(unsigned idx) const;

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
  CLASS_NAME(BaseType);
  USE_ALLOCATOR(BaseType);

  virtual ~BaseType();

  unsigned arg(unsigned idx) const
  {
    CALL("BaseType::arg");
    return (*_args)[idx];
  }

  unsigned arity() const { return _args ? _args->length() : 0; }
  virtual bool isSingleSortType(unsigned sort) const;
  bool isAllDefault() const { return isSingleSortType(Sorts::SRT_DEFAULT); }

  virtual bool isFunctionType() const { return false; }

  bool operator==(const BaseType& o) const;
  bool operator!=(const BaseType& o) const { return !(*this==o); }

  virtual vstring toString() const = 0;

  static BaseType* makeType(unsigned arity, const unsigned* domainSorts, unsigned rangeSort);
  static BaseType* makeType0(unsigned rangeSort);
  static BaseType* makeType1(unsigned arg1Sort, unsigned rangeSort);
  static BaseType* makeType2(unsigned arg1Sort, unsigned arg2Sort, unsigned rangeSort);
  static BaseType* makeType3(unsigned arg1Sort, unsigned arg2Sort, unsigned arg3Sort, unsigned rangeSort);
  static BaseType* makeTypeUniformRange(unsigned arity, unsigned argsSort, unsigned rangeSort);
protected:
  BaseType(unsigned arity, const unsigned* sorts=0);

  vstring argsToString() const;
private:
  typedef Vector<unsigned> SortVector;
  SortVector* _args;
};

class PredicateType : public BaseType
{
public:
  CLASS_NAME(PredicateType);
  USE_ALLOCATOR(PredicateType);

  PredicateType(unsigned arity, const unsigned* argumentSorts = 0)
   : BaseType(arity, argumentSorts) {}

  virtual vstring toString() const;
};

class FunctionType : public BaseType
{
public:
  CLASS_NAME(FunctionType);
  USE_ALLOCATOR(FunctionType);

  FunctionType(unsigned arity, const unsigned* argumentSorts, unsigned resultSort)
   : BaseType(arity, argumentSorts), _result(resultSort) {
    // $o cannot be the return sort of a function symbol
    // rather, it should be a predicate symbol
    ASS_NEQ(resultSort, Sorts::SRT_BOOL);
  }
  FunctionType(unsigned arity);

  unsigned result() const { return _result; }

  virtual bool isSingleSortType(unsigned sort) const;
  virtual bool isFunctionType() const { return true; }

  virtual vstring toString() const;
private:
  unsigned _result;
};

}

#endif // __Sorts__
