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
 * @file Sorts.hpp
 * Defines class Sorts.
 */

#ifndef __Sorts__
#define __Sorts__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Map.hpp"
#include "Lib/Set.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"
#include "Lib/Allocator.hpp"
#include "Lib/VString.hpp"

#include "Term.hpp"

namespace Kernel {

class Sorts { //TODO remove class altogeher and rename file
public:
  CLASS_NAME(Sorts);
  USE_ALLOCATOR(Sorts);

  //Hack. Relies on the fact that there are only
  //five interpreted sorts. It is only used in FMB
  //and SubstitutionTree and should be removed once these
  //are fixed
  static const unsigned FIRST_USER_SORT = 5;

  Sorts();
  ~Sorts();

  bool addSort(TermList sort);
  TermList addSort(vstring const& name);
  vstring sortName(unsigned sort){ return _sorts[sort].toString(); }
  vstring sortName(TermList sort){ return sort.toString(); }
#if __cplusplus >= 201402L // c++14 and newer
  [[deprecated("consider using sort.term()->getId() instead of getSortNum; if you are in a situation where a variable sort does not make sense")]]
#endif
  /** returns an id unique to this sort. These ids are independent of term.getId(). These ids are a bijective mappings between `TermList`s that represent sorts and integers in [0,count()[ */
  unsigned getSortNum(TermList sort);
  /** returns the sort represented by the given id. The id must be within [0,count()[. */
  TermList getSortTerm(unsigned sort);
  unsigned count(){return (unsigned)_sorts.size(); }
  /** true if there is a sort different from built-ins */  
  bool hasSort() { return count() > FIRST_USER_SORT; }

  //once arrays are fixed and axiomatused by a fixed number of polymorphic axioms
  //_arraySorts can be deleted
  //Once finite model building is refactored (Giles Reger knows how)
  //there is no longer a need to store any sorts at all.
  void addArraySort(TermList sort){ _arraySorts->insert(sort); }
  DHSet<TermList>* getArraySorts(){
    return _arraySorts;
  }

private:
  
  TermStack _sorts;
  DHMap<TermList, unsigned> _termListsToUnsigned;
  DHSet<TermList>* _arraySorts;
};

/**
 * The OperatorType class represents the predicate and function types 
 * the only difference between the two is that a predicate type has return type
 * $o whilst a function type has any other return type.
 *
 * The class can be used to store polymorphic types which are of the form:
 * !>[alpha_0, ..., alpha_m](sort1 * ... * sortn) > return_sort where sorts can only contain variables 
 * from  in {alpha_0,...,alpha_m}. View "A Polymorphic Vampire" for more details:
 *
 * https://link.springer.com/chapter/10.1007/978-3-030-51054-1_21
 *
 * The class stores data in a Vector<TermList>*, of length 
 * num_of_arg_sorts + 1. The number of bound variables is stored in
 * a field _typeArgsArity. It is assumed that the bound variables range from
 * 0 to _typeArgsArity - 1. In order for this assumption to be valid all sorts must
 * normalised (view SortHelper::normaliseArgSorts) before being passed to a type forming 
 * function.
 *
 * The objects of this class are perfectly shared (so that equal predicate / function types correspond to equal pointers)
 * and are obtained via static methods (to guarantee the sharing). 
 */
class OperatorType
{
public:
  CLASS_NAME(OperatorType);
  USE_ALLOCATOR(OperatorType);

  class TypeHash {
  public:
    static bool equals(OperatorType* t1, OperatorType* t2)
    { return (*t1) == (*t2); }

    static unsigned hash(OperatorType* ot)
    { 
      OperatorKey& key = *ot->key();
      unsigned typeArgsArity = ot->typeArgsArity();
      return HashUtils::combine(Hash::hash(key), Hash::hash(typeArgsArity)); 
    }
  };

private:
  typedef Vector<TermList> OperatorKey; // Vector of argument sorts together with "0" appended for predicates and resultSort appended for functions
  OperatorKey* _key;
  unsigned _typeArgsArity; /** number of quantified variables of this type */
 
  // constructors kept private
  OperatorType(OperatorKey* key, unsigned vLength) : _key(key), _typeArgsArity(vLength) {}

  /**
   * Convenience functions for creating a key
   */
  static OperatorKey* setupKey(unsigned arity, const TermList* sorts);
  static OperatorKey* setupKey(std::initializer_list<TermList> sorts);
  static OperatorKey* setupKeyUniformRange(unsigned arity, TermList argsSort);

  typedef Set<OperatorType*,TypeHash> OperatorTypes;
  static OperatorTypes& operatorTypes(); // just a wrapper around a static OperatorTypes object, to ensure a correct initialization order

  static OperatorType* getTypeFromKey(OperatorKey* key, unsigned taArity);

  //static const TermList PREDICATE_FLAG;

public:
  ~OperatorType() { _key->deallocate(); }

  inline bool operator==(const OperatorType& t) const
  { return  *_key==*t._key && 
             _typeArgsArity==t._typeArgsArity; }

  static OperatorType* getPredicateType(unsigned arity, const TermList* sorts=0, unsigned taArity = 0) {
    CALL("OperatorType::getPredicateType(unsigned,const unsigned*)");

    OperatorKey* key = setupKey(arity,sorts);
    (*key)[arity] = Term::boolSort();
    return getTypeFromKey(key,taArity);
  }

  static OperatorType* getPredicateType(std::initializer_list<TermList> sorts, unsigned taArity = 0) {
    CALL("OperatorType::getPredicateType(std::initializer_list<unsigned>)");

    OperatorKey* key = setupKey(sorts);
    (*key)[sorts.size()] = Term::boolSort();
    return getTypeFromKey(key,taArity);
  }

  static OperatorType* getPredicateTypeUniformRange(unsigned arity, TermList argsSort, unsigned taArity = 0) {
    CALL("OperatorType::getPredicateTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort);
    (*key)[arity] = Term::boolSort();
    return getTypeFromKey(key, taArity);
  }

  static OperatorType* getFunctionType(unsigned arity, const TermList* sorts, TermList resultSort, unsigned taArity = 0) {
    CALL("OperatorType::getFunctionType");

    OperatorKey* key = setupKey(arity,sorts);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key, taArity);
  }

  static OperatorType* getFunctionType(std::initializer_list<TermList> sorts, TermList resultSort, unsigned taArity = 0) {
    CALL("OperatorType::getFunctionType(std::initializer_list<unsigned>)");
 
    OperatorKey* key = setupKey(sorts);
    (*key)[sorts.size()] = resultSort;
    return getTypeFromKey(key,taArity);
  }

  static OperatorType* getFunctionTypeUniformRange(unsigned arity, TermList argsSort, TermList resultSort, unsigned taArity = 0) {
    CALL("OperatorType::getFunctionTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key,taArity);
  }

  /**
   * Convenience function for creating OperatorType for constants (as symbols).
   * Constants are function symbols of 0 arity, so just provide the result sort.
   */
  static OperatorType* getConstantsType(TermList resultSort, unsigned taArity = 0) {
    return getFunctionType(0,nullptr,resultSort, taArity); 
  }

  OperatorKey* key() const { return _key; }
  unsigned typeArgsArity() const { return _typeArgsArity; }
  unsigned arity() const { return _typeArgsArity + _key->length()-1; }

  /**
   * These are the free variables of the sorts of the arguments (and the return type in case of functions) in the polymorphic case.
   *
   * For the non-polymorphic case, _typeArgsArity==0 and this function cannot be used meaninfully.
   */
  TermList quantifiedVar(unsigned idx) const
  {
    CALL("OperatorType::quantifiedVar");
    ASS(idx < _typeArgsArity);
    return TermList(idx, false);
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
      return Term::superSort();
    } 
    return (*_key)[idx - _typeArgsArity];
  }

  //TODO functions below do not hold for higher-order
  //In higher-order we have boolean functions
  bool isPredicateType() const { return (*_key)[arity() - typeArgsArity()] == Term::boolSort(); };
  bool isFunctionType() const { return (*_key)[arity() - typeArgsArity()] != Term::boolSort(); };

  /**
   * The result sort of function types; or Term::boolSort() for predicates.
   */
  TermList result() const {
    CALL("OperatorType::result");
    return (*_key)[arity() - typeArgsArity()];
  }
  
  vstring toString() const;  

  bool isSingleSortType(TermList sort) const;
  bool isAllDefault() const { return isSingleSortType(Term::defaultSort()); }

private:
  vstring argsToString() const;
};

}

#endif // __Sorts__
