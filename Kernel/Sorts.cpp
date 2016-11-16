/**
 * @file Sorts.cpp
 * Implements class Sorts for handling collections of sorts.
 */

#include "Lib/Environment.hpp"
#include "Kernel/Theory.hpp"
#include "Shell/Options.hpp"

#include "Sorts.hpp"

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

  aux = addSort("$i");
  ASS_EQ(aux, SRT_DEFAULT);

  aux = addSort("$o");
  ASS_EQ(aux, SRT_BOOL);

  aux = addSort("$int");
  ASS_EQ(aux, SRT_INTEGER);

  aux = addSort("$rat");
  ASS_EQ(aux, SRT_RATIONAL);

  aux = addSort("$real");
  ASS_EQ(aux, SRT_REAL);

  aux = addSort("$fus");
  ASS_EQ(aux,FIRST_USER_SORT);
    
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
unsigned Sorts::addSort(const vstring& name)
{
  CALL("Sorts::addSort/1");
  bool dummy;
  return addSort(name, dummy);
} // Sorts::addSort

/**
 * Add a new or exising sort named @c name. Set @c added to true iff
 * the sort turned out to be new.
 * @author Andrei Voronkov
 */
unsigned Sorts::addSort(const vstring& name, bool& added)
{
  CALL("Sorts::addSort/2");

  unsigned result;
  if (_sortNames.find(name,result)) {
    added = false;
    return result;
  }
  _hasSort = true;
  result = _sorts.length();
  _sorts.push(new SortInfo(name, result));
  _sortNames.insert(name, result);
  added = true;
  return result;
} // Sorts::addSort


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
  VirtualIterator<SortInfo*> arraySorts = pvi(getFilteredIterator(all,
               [ss](SortInfo* s){ return s->hasStructuredSort(ss);}));
  //auto map = ([](SortInfo* s)->unsigned{ return s->id(); });
  return pvi(getMappingIterator(arraySorts,SortInfoToInt()));
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
 * Initialise a base type. If @c sorts is is NULL, all arguments will be
 * initalised by the default sort, otherwise, by sorts from the array @c sorts
 * @author Andrei Voronkov
 */
BaseType::BaseType(unsigned arity, const unsigned* sorts)
{
  CALL("BaseType::BaseType");

  if (!arity) {
    _args = 0;
    return;
  }

  _args = SortVector::allocate(arity);
  if (!sorts) {
    // initialise all argument types to the default type
    for (unsigned i = 0; i < arity; i++) {
      (*_args)[i] = Sorts::SRT_DEFAULT;
    }
    return;
  }
  // initialise all the argument types to thos taken from sorts
  for (unsigned i = 0; i < arity; i++) {
    (*_args)[i] = sorts[i];
  }
} // BaseType::BaseType

/**
 * Initialise a base type from an initializer list of sorts.
 */
BaseType::BaseType(std::initializer_list<unsigned> sorts)
{
  CALL("BaseType::BaseType");

  if (sorts.size() == 0) {
    _args = 0;
    return;
  }

  _args = SortVector::allocate(sorts.size());
  // initialise all the argument types to thos taken from sorts
  unsigned i = 0;
  for (auto sort : sorts) {
    (*_args)[i++] = sort;
  }
} // BaseType::BaseType

/**
 * Destrory the type and deallocate its arguments, if any
 * @author Andrei Voronkov 
 */ 
BaseType::~BaseType()
{
  CALL("BaseType::~BaseType");

  if (_args) {
    _args->deallocate();
  }
} // BaseType::~BaseType

/**
 * True if all arguments of this type have sort @c str.
 * @author Andrei Voronkov 
 */ 
bool BaseType::isSingleSortType(unsigned srt) const
{
  CALL("BaseType::isAllDefault");

  unsigned len = arity();
  for (unsigned i = 0; i <len; i++) {
    if (arg(i) != srt) {
      return false;
    }
  }
  return true;
} // isSingleSortType

/**
 * Return true if two types are equal. Two are are equal if their argument types
 * coincide and their return types coincide.
 * @author Andrei Voronkov
 */
bool BaseType::operator==(const BaseType& o) const
{
  CALL("BaseType::operator==");

  if (isFunctionType() != o.isFunctionType()) {
    return false;
  }
  if (isFunctionType()) {
    if (static_cast<const FunctionType&>(*this).result() != 
	static_cast<const FunctionType&>(o).result()) {
      return false;
    }
  }
  unsigned len = arity();
  if (len != o.arity()) {
    return false;
  }
  for (unsigned i=0; i < len; i++) {
    if (arg(i) != o.arg(i)) {
      return false;
    }
  }
  return true;
} // BaseType::operator==

/** 
 * Return the string representation of arguments of a non-atomic
 * functional or a predicate sort in the form (t1 * ... * tn)
 * @since 04/05/2013 bug fix (comma was used instead of *)
 * @author Andrei Voronkov
 */
vstring BaseType::argsToString() const
{
  CALL("BaseType::argsToString");

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
} // BaseType::argsToString()

/**
 * Return the TPTP string representation of the predicate type.
 * @author Andrei Voronkov
 */
vstring PredicateType::toString() const
{
  CALL("PredicateType::toString");
  return arity() ? argsToString() + " > $o" : "$o";
} // PredicateType::toString

/**
 * Create a type of the form (argSort * ... * argSort) -> rangeSort
 * @author Evgeny Kotelnikov
 */
PredicateType* PredicateType::makeTypeUniformRange(unsigned arity, unsigned argsSort)
{
  CALL("PredicateType::makeTypeUniformRange");

  static Stack<unsigned> argSorts;
  argSorts.reset();
  for (unsigned i=0; i<arity; i++) {
    argSorts.push(argsSort);
  }
  return new PredicateType(arity, argSorts.begin());
} // PredicateType::makeTypeUniformRange


/**
 * Return the TPTP string representation of the function type.
 * @author Andrei Voronkov
 */
vstring FunctionType::toString() const
{
  CALL("FunctionType::toString");
  return (arity() ? argsToString() + " > " : "") + env.sorts->sortName(result());
} // FunctionType::toString

/**
 * True if this function type has the form (srt * ... * srt) -> srt
 * @author Andrei Voronkov
 */
bool FunctionType::isSingleSortType(unsigned srt) const
{
  CALL("FunctionType::isSingleSortType");

  if (result() != srt) {
    return false;
  }
  return BaseType::isSingleSortType(srt);
} // FunctionType::isSingleSortType

/**
 * Create a type of the form (argSort * ... * argSort) -> rangeSort
 * @author Andrei Voronkov
 * @author Evgeny Kotelnikov, move to FunctionType
 */
FunctionType* FunctionType::makeTypeUniformRange(unsigned arity, unsigned argsSort, unsigned rangeSort)
{
  CALL("FunctionType::makeTypeUniformRange");

  static Stack<unsigned> argSorts;
  argSorts.reset();
  for (unsigned i=0; i<arity; i++) {
    argSorts.push(argsSort);
  }
  return new FunctionType(arity, argSorts.begin(), rangeSort);
} // FunctionType::makeTypeUniformRange
