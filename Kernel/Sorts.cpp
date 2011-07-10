/**
 * @file Sorts.cpp
 * Implements class Sorts.
 */

#include "Lib/Environment.hpp"

#include "Sorts.hpp"

namespace Kernel
{

const unsigned Sorts::SRT_DEFAULT = 0;
const unsigned Sorts::SRT_BOOL = 1;
const unsigned Sorts::SRT_INTEGER = 2;
const unsigned Sorts::SRT_RATIONAL = 3;
const unsigned Sorts::SRT_REAL = 4;
const unsigned Sorts::FIRST_USER_SORT = 5;


Sorts::Sorts()
{
  CALL("Sorts::Sorts");

  unsigned aux;

  aux = addSort("$i");
  ASS_EQ(aux, SRT_DEFAULT);

  aux = addSort("$bool");
  ASS_EQ(aux, SRT_BOOL);

  aux = addSort("$int");
  ASS_EQ(aux, SRT_INTEGER);

  aux = addSort("$rat");
  ASS_EQ(aux, SRT_RATIONAL);

  aux = addSort("$real");
  ASS_EQ(aux, SRT_REAL);
}

Sorts::~Sorts()
{
  CALL("Sorts::~Sorts");

  while(_sorts.isNonEmpty()) {
    delete _sorts.pop();
  }
}

unsigned Sorts::addSort(const string& name)
{
  bool dummy;
  return addSort(name, dummy);
}

/**
 * Return number of sort named @c name. Set @c added to true iff
 * a new sort had to be added.
 */
unsigned Sorts::addSort(const string& name, bool& added)
{
  CALL("Sorts::addSort");

  unsigned result;
  if (_sortNames.find(name,result)) {
    added = false;
    return result;
  }
  result = _sorts.length();
  _sorts.push(new SortInfo(name));
  _sortNames.insert(name,result);
  added = true;
  return result;
}


//////////////////////
// BaseType
//

BaseType* BaseType::makeType(unsigned arity, unsigned* domainSorts, unsigned rangeSort)
{
  CALL("BaseType::makeType");

  if(rangeSort==Sorts::SRT_BOOL) {
    return new PredicateType(arity, domainSorts);
  }
  else {
    return new FunctionType(arity, domainSorts, rangeSort);
  }
}

BaseType::BaseType(unsigned arity, unsigned* sorts)
{
  CALL("BaseType::BaseType");

  if(!arity) {
    _args = 0;
    return;
  }

  _args = SortVector::allocate(arity);
  if(!sorts) {
    for(unsigned i=0; i<arity; i++) {
      (*_args)[i] = Sorts::SRT_DEFAULT;
    }
  }
  else {
    for(unsigned i=0; i<arity; i++) {
      (*_args)[i] = sorts[i];
    }
  }
}

BaseType::~BaseType()
{
  CALL("BaseType::~BaseType");

  if(_args) {
    _args->deallocate();
  }
}

bool BaseType::isAllDefault() const
{
  CALL("BaseType::isAllDefault");

  unsigned len = arity();
  for(unsigned i=0; i<len; i++) {
    if(arg(i)!=Sorts::SRT_DEFAULT) {
      return false;
    }
  }
  return true;
}

bool BaseType::operator==(const BaseType& o) const
{
  CALL("BaseType::operator==");

  if(isFunctionType()!=o.isFunctionType()) {
    return false;
  }
  if(isFunctionType()) {
    if(static_cast<const FunctionType&>(*this).result()!=static_cast<const FunctionType&>(o).result()) {
      return false;
    }
  }
  unsigned len = arity();
  for(unsigned i=0; i<len; i++) {
    if(arg(i)!=o.arg(i)) {
      return false;
    }
  }
  return true;
}

FunctionType::FunctionType(unsigned arity)
 : BaseType(arity)
{
  CALL("FunctionType::FunctionType");

  _result = Sorts::SRT_DEFAULT;
}

bool FunctionType::isAllDefault() const
{
  CALL("FunctionType::isAllDefault");

  if(result()!=Sorts::SRT_DEFAULT) {
    return false;
  }
  return BaseType::isAllDefault();
}


}
