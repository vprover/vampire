/**
 * @file Sorts.cpp
 * Implements class Sorts.
 */

#include "Lib/Environment.hpp"

#include "Sorts.hpp"

namespace Kernel
{

Sorts::Sorts()
{
  CALL("Sorts::Sorts");

  unsigned defIdx = addSort("$all");
  ASS_EQ(defIdx, 0);
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

BaseType::BaseType(unsigned arity, unsigned* sorts)
{
  CALL("BaseType::BaseType");

  if(!arity) {
    _args = 0;
    return;
  }

  _args = SortVector::allocate(arity);
  if(!sorts) {
    unsigned def = env.sorts->defaultSort();
    for(unsigned i=0; i<arity; i++) {
      (*_args)[i] = def;
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

FunctionType::FunctionType(unsigned arity)
 : BaseType(arity)
{
  CALL("FunctionType::FunctionType");

  _result = env.sorts->defaultSort();
}


}
