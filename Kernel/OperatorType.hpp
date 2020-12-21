/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file OperatorType.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Map.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"

#include "Term.hpp"

namespace Kernel {

/**
 * The OperatorType class represents the predicate and function types 
 * the only difference between the two is that a predicate type has return type
 * $o whilst a function type has any other return type.
 *
 * The class can be used to store polymorphic types which are of the form:
 * !>[vars](sort1 * ... * sortn) > return_sort where sorts can only contain variables 
 * from vars. View "A Polymorphic Vampire" for more details:
 *
 * https://link.springer.com/chapter/10.1007/978-3-030-51054-1_21
 *
 * The class stores data in a Vector<TermList>*, of length num_of_bound_vars +
 * num_of_sorts + 1. In the monomorphic case, num_of_bound_vars = 0 and each
 * sort_i is a constant.
 *
 * The objects of this class are perfectly shared (so that equal predicate / function types correspond to equal pointers)
 * and are obtained via static methods (to guarantee the sharing).
 *
 * Currently, bound variables are passed to functions in this class by a pointer to a list
 * of unsigneds (representing the bound vars). To enable perfect sharing, these lists 
 * are then converted into TermLists and stored at the beginning of the vector as 
 * mentioned above. 
 */
class OperatorType
{
public:
  CLASS_NAME(OperatorType);
  USE_ALLOCATOR(OperatorType);

private:
  typedef Vector<TermList> OperatorKey; // Vector of argument sorts together with "0" appended for predicates and resultSort appended for functions
  OperatorKey* _key;
  unsigned _typeArgsArity; /** quantified variables of type */
 
  // constructors kept private
  OperatorType(OperatorKey* key, unsigned vLength) : _key(key), _typeArgsArity(vLength) {}

  /**
   * Convenience functions for creating a key
   */
  static OperatorKey* setupKey(unsigned arity, const TermList* sorts, VList* vars);
  static OperatorKey* setupKey(std::initializer_list<TermList> sorts, VList* vars);
  static OperatorKey* setupKeyUniformRange(unsigned arity, TermList argsSort, VList* vars);

  typedef Map<OperatorKey*,OperatorType*,PointerDereferencingHash> OperatorTypes;
  static OperatorTypes& operatorTypes(); // just a wrapper around a static OperatorTypes object, to ensure a correct initialization order

  static OperatorType* getTypeFromKey(OperatorKey* key, VList* vars);

  //static const TermList PREDICATE_FLAG;

public:
  ~OperatorType() { _key->deallocate(); }

  static OperatorType* getPredicateType(unsigned arity, const TermList* sorts=0, VList* vars=0) {
    CALL("OperatorType::getPredicateType(unsigned,const unsigned*)");

    OperatorKey* key = setupKey(arity,sorts,vars);
    (*key)[VList::length(vars) + arity] = AtomicSort::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getPredicateType(std::initializer_list<TermList> sorts, VList* vars = 0) {
    CALL("OperatorType::getPredicateType(std::initializer_list<unsigned>)");

    OperatorKey* key = setupKey(sorts,vars);
    (*key)[VList::length(vars) + sorts.size()] = AtomicSort::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getPredicateTypeUniformRange(unsigned arity, TermList argsSort, VList* vars = 0) {
    CALL("OperatorType::getPredicateTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort,vars);
    (*key)[VList::length(vars) + arity] = AtomicSort::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionType(unsigned arity, const TermList* sorts, TermList resultSort, VList* vars = 0) {
    CALL("OperatorType::getFunctionType");

    OperatorKey* key = setupKey(arity,sorts,vars);
    (*key)[VList::length(vars) + arity] = resultSort;
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionType(std::initializer_list<TermList> sorts, TermList resultSort, VList* vars = 0) {
    CALL("OperatorType::getFunctionType(std::initializer_list<unsigned>)");
 
    OperatorKey* key = setupKey(sorts,vars);
    (*key)[VList::length(vars) + sorts.size()] = resultSort;
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionTypeUniformRange(unsigned arity, TermList argsSort, TermList resultSort, VList* vars = 0) {
    CALL("OperatorType::getFunctionTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort,vars);
    (*key)[VList::length(vars) + arity] = resultSort;
    return getTypeFromKey(key,vars);
  }

  /**
   * Convenience function for creating OperatorType for constants (as symbols).
   * Constants are function symbols of 0 arity, so just provide the result sort.
   */
  static OperatorType* getConstantsType(TermList resultSort, VList* vars = 0) {
    return getFunctionType(0,nullptr,resultSort, vars); 
  }

  unsigned typeArgsArity() const { return _typeArgsArity; }
  unsigned arity() const { return _key->length()-1; }

  /**
   * These are the free variables of the sorts of the arguments (and the return type in case of functions) in the polymorphic case.
   *
   * For the non-polymorphic case, _typeArgsArity==0 and this function cannot be used meaninfully.
   */
  TermList quantifiedVar(unsigned idx) const
  {
    CALL("OperatorType::quantifiedVar");
    ASS(idx < _typeArgsArity);
    return (*_key)[idx];
  }

   /**
    * In the polymorhpic case, the first _typeArgsArity arguments of a predicate / function symbol are actually sorts, so their sort is "superSort"
    *
    * For idx >= _typeArgsArity (== 0 in the non-polymorphic case) this returns the actual sort of the idx-th argument
    */
  TermList arg(unsigned idx) const
  {
    CALL("OperatorType::arg");
    if(idx < _typeArgsArity){
      return AtomicSort::superSort();
    } 
    return (*_key)[idx];
  }

  //TODO functions below do not hold for higher-order
  //In higher-order we have boolean functions
  bool isPredicateType() const { return (*_key)[arity()] == AtomicSort::boolSort(); };
  bool isFunctionType() const { return (*_key)[arity()] != AtomicSort::boolSort(); };

  /**
   * The result sort of function types; or AtomicSort::boolSort() for predicates.
   */
  TermList result() const {
    CALL("OperatorType::result");
    //ASS(isFunctionType()); //TODO how best to deal with this?
    return (*_key)[arity()];
  }
  
  vstring toString() const;  

  bool isSingleSortType(TermList sort) const;
  bool isAllDefault() const { return isSingleSortType(AtomicSort::defaultSort()); }

private:
  vstring argsToString() const;
};

}

#endif // __Sorts__
