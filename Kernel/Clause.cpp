/**
 * @file Clause.cpp
 * Implements class Clause for units consisting of clauses
 *
 * @since 18/05/2007 Manchester
 */

#include <ostream>

#include "../Lib/Allocator.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Stack.hpp"

#include "Inference.hpp"
#include "Clause.hpp"
#include "Term.hpp"


using namespace Lib;
using namespace Kernel;


size_t Clause::_auxCurrTimestamp=0;
#if VDEBUG
bool Clause::_auxInUse=false;
#endif


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

bool Clause::shouldBeDestroyed()
{
  return _store==NONE && _inferenceRefCnt==0 && _inference->rule()!=Inference::INPUT;
}

/**
 * If storage is set to NONE, there are no references to this class,
 * an it is not an input clause, destroy it.
 */
void Clause::destroyIfUnnecessary()
{
  if(shouldBeDestroyed()) {
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

  static Stack<Clause*> toDestroy(32);
  Clause* cl=this;
  for(;;) {
    Inference::Iterator it = cl->_inference->iterator();
    while (cl->_inference->hasNext(it)) {
      Unit* refU=cl->_inference->next(it);
      if(!refU->isClause()) {
	continue;
      }
      Clause* refCl=static_cast<Clause*>(refU);
      refCl->_inferenceRefCnt--;
      if(refCl->shouldBeDestroyed()) {
	toDestroy.push(refCl);
      }
    }
    delete cl->_inference;
    cl->destroyExceptInferenceObject();
    if(toDestroy.isEmpty()) {
      break;
    }
    cl=toDestroy.pop();
  }
} // Clause::destroy

void Clause::destroyExceptInferenceObject()
{
  if(_literalPositions) {
    delete _literalPositions;
  }

  //We have to get sizeof(Clause) + (_length-1)*sizeof(Literal*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sizeof(Clause)+_length*sizeof(Literal*);
  size-=sizeof(Literal*);

  DEALLOC_KNOWN(this, size,"Clause");
}


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
            Int::toString(weight()) + ") " + inferenceAsString();
  return result;
} // Clause::toString


/**
 * Compute the weight of the clause.
 * @pre All literals are shared, so their weight is computed properly.
 * @since 02/01/2008 Manchester.
 */
void Clause::computeWeight() const
{
  CALL("Clause::computeWeight");

  _weight = 0;
  for (int i = _length-1; i >= 0; i--) {
    ASS(_literals[i]->shared());
    _weight += _literals[i]->weight();
  }
} // Clause::computeWeight


#if VDEBUG

void Clause::assertValid()
{
  if(_literalPositions) {
    unsigned clen=length();
    for (unsigned i = 0; i<clen; i++) {
      ASS_EQ(getLiteralPosition((*this)[i]),i);
    }
  }
}


bool Clause::contains(Literal* lit)
{
  for (int i = _length-1; i >= 0; i--) {
    if(_literals[i]==lit) {
      return true;
    }
  }
  return false;
}

#endif

std::ostream& Kernel::operator<< (ostream& out, const Clause& cl )
{
  return out<<cl.toString();
}

