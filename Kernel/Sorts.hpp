
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
  //and SubstitutioTree and should be removed once these
  //are fixed
  static const unsigned FIRST_USER_SORT = 5;

  Sorts();
  ~Sorts();

  bool addSort(TermList sort);
  vstring sortName(unsigned sort){ return _sorts[sort].toString(); }
  vstring sortName(TermList sort){ return sort.toString(); }
  unsigned getSortNum(TermList sort);
  TermList getSortTerm(unsigned sort);
  unsigned count(){return (unsigned)_sorts.size(); }
  
  //once arrays are fixed and axiomatused by a fixed number of polymorphic axioms
  //_arraySorts can be deleted
  //Once finite model buuilding is refactored (Giles Reger knows how)
  //There is no longer a need to store any sorts at all.
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

  typedef List<unsigned> VarList;

private:
  typedef Vector<TermList> OperatorKey; // Vector of argument sorts together with "0" appended for predicates and resultSort appended for functions
  OperatorKey* _key;
  unsigned _typeArgsArity; /** quantified variables of type */
 
  // constructors kept private
  OperatorType(OperatorKey* key, unsigned vLength) : _key(key), _typeArgsArity(vLength) {}

  /**
   * Convenience functions for creating a key
   */
  static OperatorKey* setupKey(unsigned arity, const TermList* sorts=0, VarList* vars = 0);
  static OperatorKey* setupKey(std::initializer_list<TermList> sorts, VarList* vars);
  static OperatorKey* setupKeyUniformRange(unsigned arity, TermList argsSort, VarList* vars);

  typedef Map<OperatorKey*,OperatorType*,PointerDereferencingHash> OperatorTypes;
  static OperatorTypes& operatorTypes(); // just a wrapper around a static OperatorTypes object, to ensure a correct initialization order

  static OperatorType* getTypeFromKey(OperatorKey* key, VarList* vars);

  //static const TermList PREDICATE_FLAG;

public:
  ~OperatorType() { _key->deallocate(); }

  static OperatorType* getPredicateType(unsigned arity, const TermList* sorts=0, VarList* vars=0) {
    CALL("OperatorType::getPredicateType(unsigned,const unsigned*)");

    OperatorKey* key = setupKey(arity,sorts,vars);
    (*key)[arity] = Term::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getPredicateType(std::initializer_list<TermList> sorts, VarList* vars = 0) {
    CALL("OperatorType::getPredicateType(std::initializer_list<unsigned>)");

    OperatorKey* key = setupKey(sorts,vars);
    (*key)[VList::length(vars) + sorts.size()] = Term::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getPredicateTypeUniformRange(unsigned arity, TermList argsSort, VarList* vars = 0) {
    CALL("OperatorType::getPredicateTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort,vars);
    (*key)[arity] = Term::boolSort();
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionType(unsigned arity, const TermList* sorts, TermList resultSort, VarList* vars = 0) {
    CALL("OperatorType::getFunctionType");

    OperatorKey* key = setupKey(arity,sorts,vars);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionType(std::initializer_list<TermList> sorts, TermList resultSort, VarList* vars = 0) {
    CALL("OperatorType::getFunctionType(std::initializer_list<unsigned>)");
 
    OperatorKey* key = setupKey(sorts,vars);
    (*key)[VList::length(vars) + sorts.size()] = resultSort;
    return getTypeFromKey(key,vars);
  }

  static OperatorType* getFunctionTypeUniformRange(unsigned arity, TermList argsSort, TermList resultSort, VarList* vars = 0) {
    CALL("OperatorType::getFunctionTypeUniformRange");

    OperatorKey* key = setupKeyUniformRange(arity,argsSort,vars);
    (*key)[arity] = resultSort;
    return getTypeFromKey(key,vars);
  }

  /**
   * Convenience function for creating OperatorType for constants (as symbols).
   * Constants are function symbols of 0 arity, so just provide the result sort.
   */
  static OperatorType* getConstantsType(TermList resultSort, VarList* vars = 0) { 
    return getFunctionType(0,nullptr,resultSort, vars); 
  }

  unsigned typeArgsArity() const { return _typeArgsArity; }
  unsigned arity() const { return _key->length()-1; }

  TermList quantifiedVar(unsigned idx) const
  {
    CALL("OperatorType::quantifiedVar");
    ASS(idx < _typeArgsArity);
    return (*_key)[idx];
  }

  TermList arg(unsigned idx) const
  {
    CALL("OperatorType::arg");
    if(idx < _typeArgsArity){
      return Term::superSort();
    } 
    return (*_key)[idx];
  }

  //TODO functions below do not hold for higher-order
  //In higher-order we have boolean functions
  bool isPredicateType() const { return (*_key)[arity()] == Term::boolSort(); };
  bool isFunctionType() const { return (*_key)[arity()] != Term::boolSort(); };
  TermList result() const {
    CALL("OperatorType::result");
    //ASS(isFunctionType()); //TODO how best to deal with this?
    return (*_key)[arity()];
  }
  
  vstring toString() const;  

  bool isSingleSortType(TermList sort) const;
  bool isAllDefault() const { return isSingleSortType(Term::defaultSort()); }

private:
  vstring argsToString() const;
};

}

#endif // __Sorts__
