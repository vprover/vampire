
/*
 * File Sorts.cpp.
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
 * @file Sorts.cpp
 * Implements class Sorts for handling collections of sorts.
 */

#include "Sorts.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Theory.hpp"
#include "Shell/Options.hpp"

#include "Signature.hpp"

using namespace Kernel;

/**
 * Initialise sorts by adding the default sort
 * @since 04/05/2013 Manchester, updated with the new built-in sorts
 * @author Andrei Voronkov
 */
Sorts::Sorts()
{
  CALL("Sorts::Sorts");

  unsigned aux;

  aux = addSort("$i",true);
  ASS_EQ(aux, SRT_DEFAULT);

  aux = addSort("$o",true);
  ASS_EQ(aux, SRT_BOOL);

  aux = addSort("$int",true);
  ASS_EQ(aux, SRT_INTEGER);

  aux = addSort("$rat",true);
  ASS_EQ(aux, SRT_RATIONAL);

  aux = addSort("$real",true);
  ASS_EQ(aux, SRT_REAL);
    
 _hasSort = false;
} // Sorts::Sorts

/**
 * Destroy the object and delete all sorts in it.
 * @author Andrei Voronkov
 */
Sorts::~Sorts()
{
  CALL("Sorts::~Sorts");

  while(_sorts.isNonEmpty()) {
    delete _sorts.pop();
  }
} // Sorts::~Sorts

/**
 * Add a new or existing sort and return its number.
 * @author Andrei Voronkov
 */
unsigned Sorts::addSort(const vstring& name, bool interpreted)
{
  CALL("Sorts::addSort/2");
  bool dummy;
  return addSort(name, dummy, interpreted);
} // Sorts::addSort

Sorts::SortInfo::SortInfo(const vstring& name,const unsigned id, bool interpreted)
{
  CALL("Sorts::SortInfo::SortInfo");

  if (Signature::symbolNeedsQuoting(name,interpreted,0)) { // arity does not make sense for sorts, but the code still should
    _name = "'" + name + "'";
  } else {
    _name = name;
  }

  _id = id;
}

/**
 * Add a new or exising sort named @c name. Set @c added to true iff
 * the sort turned out to be new.
 * @author Andrei Voronkov
 */
unsigned Sorts::addSort(const vstring& name, bool& added, bool interpreted)
{
  CALL("Sorts::addSort/3");

  unsigned result;
  if (_sortNames.find(name,result)) {
    added = false;
    return result;
  }
  _hasSort = true;
  result = _sorts.length();
  _sorts.push(new SortInfo(name, result,interpreted));
  _sortNames.insert(name, result);
  added = true;
  return result;
} // Sorts::addSort


unsigned Sorts::addBitVectorSort(const unsigned size)
{
    CALL("Sorts::addBitVectorSort");
    
    vstring name = "$bitVector(" + Int::toString(size) + ")";
    
    unsigned result;
    if(_sortNames.find(name,result))
        return result;
    
    _hasSort = true;
    result = _sorts.length();
    
    BitVectorSort* sort = new BitVectorSort(name,size,result);
    _sorts.push(sort);
    _sortNames.insert(name,result);
    
    return result;
}

/**
 *
 * @author Giles
 */
unsigned Sorts::addArraySort(const unsigned indexSort, const unsigned innerSort)
{
  CALL("Sorts::addArraySort");

  vstring name = "$array(";
  name+=env.sorts->sortName(indexSort);
  name+=",";
  name+=env.sorts->sortName(innerSort);
  name+=")";
  unsigned result;
  if(_sortNames.find(name,result)){
    return result;
  }

  _hasSort = true;
  result = _sorts.length(); 

  ArraySort* sort = new ArraySort(name,indexSort,innerSort,result);
  _sorts.push(sort);
  _sortNames.insert(name,result);

  return result;
}

struct SortInfoToInt{
  DECL_RETURN_TYPE(unsigned);
  unsigned operator()(Sorts::SortInfo* s){ return s->id(); }
};

/**
 * @authors Giles, Evgeny
 */
VirtualIterator<unsigned> Sorts::getStructuredSorts(const StructuredSort ss)
{
  CALL("Sorts::getStructuredSorts");
  Stack<SortInfo*>::Iterator all(_sorts);
  VirtualIterator<SortInfo*> structuredSorts = pvi(getFilteredIterator(all,
               [ss](SortInfo* s){ return s->isOfStructuredSort(ss);}));
  return pvi(getMappingIterator(structuredSorts,SortInfoToInt()));
}

unsigned Sorts::addTupleSort(unsigned arity, unsigned sorts[])
{
  CALL("Sorts::addTupleSort");

  vstring name = "[";
  for (unsigned i = 0; i < arity; i++) {
    name += env.sorts->sortName(sorts[i]);
    if (i != arity - 1) {
      name += ",";
    }
  }
  name += "]";
  unsigned result;
  if(_sortNames.find(name, result)) {
    return result;
  }

  _hasSort = true;
  result = _sorts.length();

  _sorts.push(new TupleSort(name,result,arity,sorts));
  _sortNames.insert(name, result);

  return result;
}

/**
 * True if this collection contains the sort @c name.
 * @author Andrei Voronkov
 */
bool Sorts::haveSort(const vstring& name)
{
  CALL("Sorts::haveSort");
  return _sortNames.find(name);
} // haveSort

/**
 * Find a sort with the name @c name. If the sort is found, return true and set @c idx
 * to the sort number. Otherwise, return false.
 * @author Andrei Voronkov
 */
bool Sorts::findSort(const vstring& name, unsigned& idx)
{
  CALL("Sorts::findSort");
  return _sortNames.find(name, idx);
} // Sorts::findSort

const vstring& Sorts::sortName(unsigned idx) const
{
  CALL("Sorts::sortName");
  if (env.options->showFOOL() && idx == SRT_BOOL) {
    static vstring name("$bool");
    return name;
  }
  return _sorts[idx]->name();
} // Sorts::sortName

/**
 * Pre-initialise an OperatorKey.
 *
 * If @c sorts is is NULL, all arguments will be initalized by the default sort,
 * otherwise, by sorts from the array @c sorts
 * @author Andrei Voronkov
 */
OperatorType::OperatorKey* OperatorType::setupKey(unsigned arity, const unsigned* sorts)
{
  CALL("OperatorType::setupKey(unsigned,const unsigned*)");

  OperatorKey* key = OperatorKey::allocate(arity+1);

  if (!sorts) {
    // initialise all argument types to the default type
    for (unsigned i = 0; i < arity; i++) {
      (*key)[i] = Sorts::SRT_DEFAULT;
    }
  } else {
    // initialise all the argument types to those taken from sorts
    for (unsigned i = 0; i < arity; i++) {
      (*key)[i] = sorts[i];
    }
  }
  return key;
}

/**
 * Pre-initialise an OperatorKey from an initializer list of sorts.
 */
OperatorType::OperatorKey* OperatorType::setupKey(std::initializer_list<unsigned> sorts)
{
  CALL("OperatorType::setupKey(std::initializer_list<unsigned>)");

  OperatorKey* key = OperatorKey::allocate(sorts.size()+1);

  // initialise all the argument types to those taken from sorts
  unsigned i = 0;
  for (auto sort : sorts) {
    (*key)[i++] = sort;
  }

  return key;
}

/**
 * Pre-initialise an OperatorKey from using a uniform range.
 */
OperatorType::OperatorKey* OperatorType::setupKeyUniformRange(unsigned arity, unsigned argsSort)
{
  CALL("OperatorType::setupKeyUniformRange");

  OperatorKey* key = OperatorKey::allocate(arity+1);

  for (unsigned i=0; i<arity; i++) {
    (*key)[i] = argsSort;
  }

  return key;
}

OperatorType::OperatorTypes& OperatorType::operatorTypes() {
  // we should delete all the stored OperatorTypes inside at the end of the world, when this get destroyed
  static OperatorType::OperatorTypes _operatorTypes;
  return _operatorTypes;
}

/**
 * Check if OperatorType corresponding to the given key
 * already exists. If so return it, if not create new,
 * store it for future retrieval and return it.
 *
 * Release key if not needed.
 */
OperatorType* OperatorType::getTypeFromKey(OperatorType::OperatorKey* key)
{
  CALL("OperatorType::getTypeFromKey");

  /*
  cout << "getTypeFromKey(" << key->length() << "): ";
  for (unsigned i = 0; i < key->length(); i++) {
    cout << (((*key)[i] == PREDICATE_FLAG) ? "FFFF" : env.sorts->sortName((*key)[i])) << ",";
  }
  */

  OperatorType* resultType;
  if (operatorTypes().find(key,resultType)) {
    key->deallocate();

    // cout << " Found " << resultType << endl;

    return resultType;
  }

  resultType = new OperatorType(key);
  operatorTypes().insert(key,resultType);

  // cout << " Created new " << resultType << endl;

  return resultType;
}

/**
 * Return the string representation of arguments of a non-atomic
 * functional or a predicate sort in the form (t1 * ... * tn)
 * @since 04/05/2013 bug fix (comma was used instead of *)
 * @author Andrei Voronkov
 */
vstring OperatorType::argsToString() const
{
  CALL("OperatorType::argsToString");

  vstring res = "(";
  unsigned ar = arity();
  ASS(ar);
  for (unsigned i = 0; i < ar; i++) {
    res += env.sorts->sortName(arg(i));
    if (i != ar-1) {
      res += " * ";
    }
  }
  res += ')';
  return res;
} // OperatorType::argsToString()

/**
 * Return the TPTP string representation of the OpertorType.
 */
vstring OperatorType::toString() const
{
  CALL("OperatorType::toString");

  return (arity() ? argsToString() + " > " : "") +
      (isPredicateType() ? "$o" : env.sorts->sortName(result()));
}

/**
 * True if all arguments of this type have sort @c str
 * and so is the result sort if we are talking about a function type.
 * @author Andrei Voronkov
 */
bool OperatorType::isSingleSortType(unsigned srt) const
{
  CALL("OperatorType::isAllDefault");

  unsigned len = arity();
  for (unsigned i = 0; i <len; i++) {
    if (arg(i) != srt) {
      return false;
    }
  }

  if (isFunctionType() && result() != srt) {
    return false;
  }

  return true;
} // isSingleSortType
