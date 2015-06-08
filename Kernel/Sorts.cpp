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

  aux = addSort("$bool");
  ASS_EQ(aux, SRT_FOOL_BOOL);

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
  if (result == SRT_FOOL_BOOL && !env.options->showFOOL()) {
    _sorts.push(new SortInfo("$o", result));
    _sortNames.insert("$o", result);
  } else {
    _sorts.push(new SortInfo(name, result));
    _sortNames.insert(name, result);
  }
  added = true;
  return result;
} // Sorts::addSort


/**
 *
 * @author Giles
 */
unsigned Sorts::addArraySort(const unsigned innerSort)
{
  CALL("Sorts::addArraySort");

  // First check if it already exists
  vstring name = "$array["+env.sorts->sortName(innerSort)+"]";
  unsigned result;
  if(_sortNames.find(name,result)){
    return result;
  }

  // Do we need to set _hasSort?
  result = _sorts.length(); 
  // Next create ArraySort and register it
  ArraySort* sort = new ArraySort(name,innerSort,result);
  _sorts.push(sort);
  _sortNames.insert(name,result);

  // Next create and register the STORE and SELECT functions for this sort with Theory
  
  Theory::instance()->addStructuredSortInterpretation(result,Theory::StructuredSortInterpretation::ARRAY_STORE);
  Theory::instance()->addStructuredSortInterpretation(result,Theory::StructuredSortInterpretation::ARRAY_SELECT);

  // TheoryAxioms will automatically get the array sorts via getArraySorts

  // We are done
  return result;
}

struct SortInfoToInt{
  DECL_RETURN_TYPE(unsigned);
  unsigned operator()(Sorts::SortInfo* s){ return s->id(); }
};

/**
 *
 * @author Giles
 */ 
VirtualIterator<unsigned> Sorts::getArraySorts()
{
  CALL("Sorts::getArraySorts");
  Stack<SortInfo*>::Iterator all(_sorts);
  VirtualIterator<SortInfo*> arraySorts = pvi(getFilteredIterator(all,
               [](SortInfo* s){ return s->hasStructuredSort(StructuredSort::ARRAY);}));
  //auto map = ([](SortInfo* s)->unsigned{ return s->id(); });
  return pvi(getMappingIterator(arraySorts,SortInfoToInt()));
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

/**
 * Create a type having arity @c arity, range sort @c rangeSort and arguments
 * from the array @c domainSorts (which can be NULL)
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeType(unsigned arity, const unsigned* domainSorts, unsigned rangeSort)
{
  CALL("BaseType::makeType");

  if (rangeSort==Sorts::SRT_BOOL) {
    return new PredicateType(arity, domainSorts);
  }
  else {
    return new FunctionType(arity, domainSorts, rangeSort);
  }
} // BaseType::makeType

/**
 * Create atomic type rangeSort
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeType0(unsigned rangeSort)
{
  CALL("BaseType::makeType0");
  return makeType(0, 0, rangeSort);
} // BaseType::makeType0

/**
 * Create type arg1Sort -> rangeSort
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeType1(unsigned arg1Sort, unsigned rangeSort)
{
  CALL("BaseType::makeType1");

  unsigned args[] = { arg1Sort };
  return makeType(1, args, rangeSort);
} // BaseType::makeType1

/**
 * Create type (arg1Sort * arg2Sort) -> rangeSort
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeType2(unsigned arg1Sort, unsigned arg2Sort, unsigned rangeSort)
{
  CALL("BaseType::makeType2");
  unsigned args[] = { arg1Sort, arg2Sort };
  return makeType(2, args, rangeSort);
} // BaseType::makeType2

/**
 * Create type (arg1Sort * arg2Sort * arg3Sort) -> rangeSort
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeType3(unsigned arg1Sort, unsigned arg2Sort, unsigned arg3Sort, unsigned rangeSort)
{
  CALL("BaseType::makeType3");

  unsigned args[] = { arg1Sort, arg2Sort, arg3Sort };
  return makeType(3, args, rangeSort);
} // BaseType::makeType3

/**
 * Create a type of the form (argSort * ... * argSort) -> rangeSort
 * @author Andrei Voronkov
 */
BaseType* BaseType::makeTypeUniformRange(unsigned arity, unsigned argsSort, unsigned rangeSort)
{
  CALL("BaseType::makeTypeUniformRange");

  static Stack<unsigned> argSorts;
  argSorts.reset();
  for (unsigned i=0; i<arity; i++) {
    argSorts.push(argsSort);
  }
  return makeType(arity, argSorts.begin(), rangeSort);
} // BaseType::makeTypeUniformRange

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
    /**
     * A function argument cannot have sort SRT_BOOL.
     * It can be SRT_FOOL_BOOL, though.
     */
    ASS_NEQ(sorts[i], Sorts::SRT_BOOL);
    (*_args)[i] = sorts[i];
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
  return (arity() ? argsToString() + " > " : "") + env.sorts->sortName(Sorts::SRT_BOOL);
} // PredicateType::toString

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
 * Create a function type of arity @c arity. The arguments and the result
 * type set to the default type.
 * @author Andrei Voronkov
 */
FunctionType::FunctionType(unsigned arity)
 : BaseType(arity)
{
  CALL("FunctionType::FunctionType");
  _result = Sorts::SRT_DEFAULT;
} // FunctionType::FunctionType

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
