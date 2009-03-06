/**
 * @file Clause.cpp
 * Implements class Clause for units consisting of clauses
 *
 * @since 18/05/2007 Manchester
 */

#include "../Lib/Allocator.hpp"
#include "../Lib/Int.hpp"

#include "Inference.hpp"
#include "Clause.hpp"
#include "Term.hpp"

#if VDEBUG

#include <ostream>
#include "../Test/Output.hpp"

#endif

using namespace Lib;
using namespace Kernel;

/**
 * Allocate a clause having lits literals.
 * @since 18/05/2007 Manchester
 */
void* Clause::operator new(size_t sz,unsigned lits)
{
  CALL("Clause::operator new");

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sz+lits*sizeof(Literal*);
  size-=sizeof(Literal*);

  return ALLOC_KNOWN(size,"Clause");
}

/**
 * If storage is set to NONE, there are no references to this class,
 * an it is not an input clause, destroy it.
 *
 * @warning This method can lead to quite a deep recursion.
 */
void Clause::destroyIfUnnecessary()
{
  if(_store==NONE && _inferenceRefCnt==0 && _inference->rule()!=Inference::INPUT) {
    destroy();
  }
}

/**
 * Destroy the clause by deleting the clause itself and all of its
 * literals.
 * @since 19/05/2007 Manchester
 */
void Clause::destroy()
{
  CALL("Clause::destroy");
  _inference->destroy();

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sizeof(Clause)+_length*sizeof(Literal*);
  size-=sizeof(Literal*);

  DEALLOC_KNOWN(this, size,"Clause");
} // Clause::destroy

/**
 * Convert the clause to the string representation.
 * @since 20/05/2007 Manchester
 */
string Clause::toString() const
{
  CALL("Clause::toString");

  string result = Int::toString(_number) + ". ";
  if (_length == 0) {
    result += '#';
  }
  else {
    result += _literals[0]->toString();
    if (_length > 1) {
      for (unsigned i = 1; i < _length;i++) {
	result += " | ";
	result += _literals[i]->toString();
      }
    }
  }
  result += string(" (") + Int::toString(_age) + ':' +
            Int::toString(_weight) + ") " + inferenceAsString();
  return result;
} // Clause::toString


/**
 * Compute the weight of the clause.
 * @pre All literals are shared, so their weight is computed properly.
 * @since 02/01/2008 Manchester.
 */
void Clause::computeWeight()
{
  CALL("Clause::computeWeight");

  _weight = 0;
  for (int i = _length-1; i >= 0; i--) {
    ASS(_literals[i]->shared());
    _weight += _literals[i]->weight();
  }
} // Clause::computeWeight


#if VDEBUG

bool Clause::contains(Literal* lit)
{
  for (int i = _length-1; i >= 0; i--) {
    if(_literals[i]==lit) {
      return true;
    }
  }
  return false;
}

std::ostream& Kernel::operator<< (ostream& out, const Clause& cl )
{
  return out<<cl.toString();
}

#endif
