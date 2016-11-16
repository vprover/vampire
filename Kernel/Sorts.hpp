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
    /** this is not a sort, it is just used to denote the first index of a user-define sort */
    FIRST_USER_SORT = 5
  };

  /** Various structured sorts */
  enum class StructuredSort {
    /** The structured sort for arrays **/
    ARRAY,
    /** The structured sort for lists, currently unused **/
    LIST,
    /** The structured sort for tuples */
    TUPLE,
    /** not a real structured sort, it's here to denote the length of the StructuredSort enum */
    LAST_STRUCTURED_SORT
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
      SortInfo(name,id), _sort(sort) { (void)_sort; /*to suppress warning about unused*/ }

    bool hasStructuredSort(StructuredSort sort) override {
      return sort==_sort;
    }

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
      //cout << "Creating ArraySort " << name << " with id " << id << endl; 
#endif
    }

    unsigned getIndexSort(){ return _indexSort; }
    unsigned getInnerSort(){ return _innerSort; }

  private:
    // the SortInfo can be found using Sorts
    unsigned _indexSort;
    unsigned _innerSort;

  };

  class TupleSort : public StructuredSortInfo
  {
  public:
    CLASS_NAME(TupleSort);
    USE_ALLOCATOR(TupleSort);

    TupleSort(vstring name, unsigned id, unsigned arity, unsigned sorts[])
      : StructuredSortInfo(name, StructuredSort::TUPLE, id), _arity(arity) {
      _sorts = new unsigned[arity];
      for (unsigned i = 0; i < arity; i++) {
        _sorts[i] = sorts[i];
      }
    }

    unsigned arity() const { return _arity; }
    unsigned* sorts() const { return _sorts; }
    unsigned argument(unsigned index) const { ASS_G(_arity, index); return _sorts[index]; }

  private:
    unsigned _arity;
    unsigned* _sorts;
  };

  unsigned addSort(const vstring& name, bool& added);
  unsigned addSort(const vstring& name);

  unsigned addArraySort(unsigned indexSort, unsigned innerSort);
  ArraySort* getArraySort(unsigned sort){
    ASS(hasStructuredSort(sort,StructuredSort::ARRAY));
    return static_cast<ArraySort*>(_sorts[sort]);
  }

  unsigned addTupleSort(unsigned arity, unsigned sorts[]);
  TupleSort* getTupleSort(unsigned sort) {
    ASS(hasStructuredSort(sort,StructuredSort::TUPLE));
    return static_cast<TupleSort*>(_sorts[sort]);
  }

  bool haveSort(const vstring& name);
  bool findSort(const vstring& name, unsigned& idx);

  VirtualIterator<unsigned> getStructuredSorts(const StructuredSort ss);

  bool hasStructuredSort(unsigned sort) {
    if(sort > _sorts.size()) return false;
    unsigned sorts = (unsigned)StructuredSort::LAST_STRUCTURED_SORT;
    for (unsigned ss = 0; ss < sorts; ss++) {
      if (_sorts[sort]->hasStructuredSort(static_cast<StructuredSort>(ss))) {
        return true;
      }
    }
    return false;
  }

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
protected:
  BaseType(unsigned arity, const unsigned* sorts=0);
  BaseType(std::initializer_list<unsigned> sorts);

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

  PredicateType(unsigned arity, const unsigned* argumentSorts)
   : BaseType(arity, argumentSorts) {}
  PredicateType(std::initializer_list<unsigned> sorts) : BaseType(sorts) {}

  virtual vstring toString() const;

  static PredicateType* makeTypeUniformRange(unsigned arity, unsigned argsSort);
};

class FunctionType : public BaseType
{
public:
  CLASS_NAME(FunctionType);
  USE_ALLOCATOR(FunctionType);

  FunctionType(unsigned arity, const unsigned* argumentSorts, unsigned resultSort)
   : BaseType(arity, argumentSorts), _result(resultSort) {}
  FunctionType(unsigned resultSort)
   : BaseType(0, 0), _result(resultSort) {}
  FunctionType(std::initializer_list<unsigned> argSorts, unsigned resultSort)
   : BaseType(argSorts), _result(resultSort) {}

  unsigned result() const { return _result; }

  virtual bool isSingleSortType(unsigned sort) const;
  virtual bool isFunctionType() const { return true; }

  virtual vstring toString() const;

  static FunctionType* makeTypeUniformRange(unsigned arity, unsigned argsSort, unsigned rangeSort);
private:
  unsigned _result;
};

}

#endif // __Sorts__
