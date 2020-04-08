
/*
 * File Sorts.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Sorts.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
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
  
    SortInfo(const vstring& name,const unsigned id, bool interpreted = false);
    virtual ~SortInfo() {}
    
    const vstring& name() const { return _name; }
    const unsigned id() const { return _id; }

    virtual bool isOfStructuredSort(StructuredSort sort) { return false; }

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

    bool isOfStructuredSort(StructuredSort sort) override {
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
      _indexSort(indexSort), _innerSort(innerSort) {}

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
      : StructuredSortInfo(name, StructuredSort::TUPLE, id), _sorts(arity) {
      for (unsigned i = 0; i < arity; i++) {
        _sorts[i] = sorts[i];
      }
    }

    unsigned arity() const { return (unsigned)_sorts.size(); }
    unsigned* sorts() { return _sorts.array(); }
    unsigned argument(unsigned index) const { ASS_G(arity(), index); return _sorts[index]; }

  private:
    DArray<unsigned> _sorts;
  };

  unsigned addSort(const vstring& name, bool& added, bool interpreted);
  unsigned addSort(const vstring& name, bool interpreted);

  unsigned addArraySort(unsigned indexSort, unsigned innerSort);
  ArraySort* getArraySort(unsigned sort){
    ASS(isOfStructuredSort(sort,StructuredSort::ARRAY));
    return static_cast<ArraySort*>(_sorts[sort]);
  }

  unsigned addTupleSort(unsigned arity, unsigned sorts[]);
  TupleSort* getTupleSort(unsigned sort) {
    ASS(isOfStructuredSort(sort,StructuredSort::TUPLE));
    return static_cast<TupleSort*>(_sorts[sort]);
  }

  bool haveSort(const vstring& name);
  bool findSort(const vstring& name, unsigned& idx);

  VirtualIterator<unsigned> getStructuredSorts(const StructuredSort ss);

  bool isStructuredSort(unsigned sort) {
    if(sort > _sorts.size()) return false;
    SortInfo* si = _sorts[sort];
    for (unsigned ss = 0; ss < (unsigned)StructuredSort::LAST_STRUCTURED_SORT; ss++) {
      if (si->isOfStructuredSort(static_cast<StructuredSort>(ss))) {
        return true;
      }
    }
    return false;
  }

  bool isOfStructuredSort(unsigned sort, StructuredSort structured){
    if(sort > _sorts.size()) return false;
    return _sorts[sort]->isOfStructuredSort(structured);
  }

  const vstring& sortName(unsigned idx) const;

  /**
   * Return the number of sorts
   */
  unsigned count() const { return _sorts.length(); }
  /** true if there is a sort different from built-ins */
  bool hasSort() const {return _hasSort;}

private:
  SymbolMap _sortNames;
  Stack<SortInfo*> _sorts;
  /** true if there is a sort different from built-ins */
  bool _hasSort;
};

/**
 * The OperatorType class represents the predicate and function types (which are not sorts in first-order logic).
 * These are determined by their kind (either PREDICATE or FUNCTION), arity, a corresponding list of argument sorts,
 * and a return sort in the case of functions.
 *
 * The class stores all this data in one Vector<unsigned>*, of length arity+1,
 * where the last element is the return sort for functions and "MAX_UNSIGNED" for predicates (which distinguishes the two kinds).
 *
 * The objects of this class are perfectly shared (so that equal predicate / function types correspond to equal pointers)
 * and are obtained via static methods (to guarantee the sharing).
 */
class OperatorType
{
public:
  CLASS_NAME(OperatorType);
  USE_ALLOCATOR(OperatorType);

private:
  typedef Vector<unsigned> OperatorKey; // Vector of argument sorts together with "FFFF" appended for predicates and resultSort appended for functions
  OperatorKey* _key;

  // constructors kept private
  OperatorType(OperatorKey* key) : _key(key) {}

  /**
   * Convenience functions for creating a key
   */
  static OperatorKey* setupKey(unsigned arity, const unsigned* sorts=0);
  static OperatorKey* setupKey(std::initializer_list<unsigned> sorts);
  static OperatorKey* setupKeyUniformRange(unsigned arity, unsigned argsSort);

  typedef Map<OperatorKey*,OperatorType*,PointerDereferencingHash> OperatorTypes;
  static OperatorTypes& operatorTypes(); // just a wrapper around a static OperatorTypes object, to ensure a correct initialization order

  static OperatorType* getTypeFromKey(OperatorKey* key);

  static const unsigned PREDICATE_FLAG = std::numeric_limits<unsigned>::max();

public:
  ~OperatorType() { _key->deallocate(); }

  static OperatorType* getPredicateType(unsigned arity, const unsigned* sorts=0) {
    CALL("OperatorType::getPredicateType(unsigned,const unsigned*)");

    OperatorKey* key = setupKey(arity,sorts);
    (*key)[arity] = PREDICATE_FLAG;
    return getTypeFromKey(key);
  }

  static OperatorType* getPredicateType(std::initializer_list<unsigned> sorts) {
    CALL("OperatorType::getPredicateType(std::initializer_list<unsigned>)");

    OperatorKey* key = setupKey(sorts);
    (*key)[sorts.size()] = PREDICATE_FLAG;
    return getTypeFromKey(key);
  }

  static OperatorType* getPredicateTypeUniformRange(unsigned arity, unsigned argsSort) {
    CALL("OperatorType::getPredicateTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort);
    (*key)[arity] = PREDICATE_FLAG;
    return getTypeFromKey(key);
  }

  static OperatorType* getFunctionType(unsigned arity, const unsigned* sorts, unsigned resultSort) {
    CALL("OperatorType::getFunctionType");

    OperatorKey* key = setupKey(arity,sorts);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key);
  }

  static OperatorType* getFunctionType(std::initializer_list<unsigned> sorts, unsigned resultSort) {
    CALL("OperatorType::getFunctionType(std::initializer_list<unsigned>)");

    OperatorKey* key = setupKey(sorts);
    (*key)[sorts.size()] = resultSort;
    return getTypeFromKey(key);
  }

  static OperatorType* getFunctionTypeTypeUniformRange(unsigned arity, unsigned argsSort, unsigned resultSort) {
    CALL("OperatorType::getFunctionTypeTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key);
  }

  /**
   * Convenience function for creating OperatorType for constants (as symbols).
   * Constants are function symbols of 0 arity, so just provide the result sort.
   */
  static OperatorType* getConstantsType(unsigned resultSort) { return getFunctionType(0,nullptr,resultSort); }

  unsigned arity() const { return _key->length()-1; }

  unsigned arg(unsigned idx) const
  {
    CALL("OperatorType::arg");
    return (*_key)[idx];
  }

  bool isPredicateType() const { return (*_key)[arity()] == PREDICATE_FLAG; };
  bool isFunctionType() const { return (*_key)[arity()] != PREDICATE_FLAG; };
  unsigned result() const {
    CALL("OperatorType::result");
    ASS(isFunctionType());
    return (*_key)[arity()];
  }

  vstring toString() const;

  bool isSingleSortType(unsigned sort) const;
  bool isAllDefault() const { return isSingleSortType(Sorts::SRT_DEFAULT); }

private:
  vstring argsToString() const;
};

}

#endif // __Sorts__
