/**
 * @file SATClause.cpp
 * Implements class SATClause.
 */

#include <algorithm>
#include <ostream>

#include "../Lib/Allocator.hpp"
#include "../Lib/Int.hpp"

//#include "Inference.hpp"

#include "SATClause.hpp"


namespace SAT {

using namespace Lib;

/**
 * Allocate a clause having lits literals.
 * @since 18/05/2007 Manchester
 */
void* SATClause::operator new(size_t sz,unsigned lits)
{
  CALL("SATKernel::SATClause::operator new");

  //We have to get sizeof(SATClause) + (_length-1)*sizeof(SATLiteral*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sz+lits*sizeof(SATLiteral);
  size-=sizeof(SATLiteral);

  return ALLOC_KNOWN(size,"SATClause");
}

/**
 * Destroy the clause by deleting the clause itself and all of its
 * literals.
 *
 * Only clauses that aren't referenced by any Inference object should
 * be deleted.
 */
void SATClause::destroy()
{
  CALL("SATKernel::SATClause::destroy");

#if !NO_CLAUSE_INFO
  _inference->destroy();
#endif

  //We have to get sizeof(SATClause) + (_length-1)*sizeof(SATLiteral*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sizeof(SATClause)+_length*sizeof(SATLiteral);
  size-=sizeof(SATLiteral);

  DEALLOC_KNOWN(this, size,"SATClause");
} // SATClause::destroy


bool litComparator(SATLiteral l1, SATLiteral l2)
{
  return l1.content()>l2.content();
}

/**
 * Sort literals in descending order.
 */
void SATClause::sort()
{
  std::sort(&_literals[0], &_literals[length()], litComparator);
}


/**
 * Convert the clause to the string representation.
 * @since 20/05/2007 Manchester
 */
string SATClause::toString() const
{
  CALL("SATKernel::SATClause::toString");

  string result;
  if (_length == 0) {
    result = "#";
  } else {
    result = _literals[0].toString();
    if (_length > 1) {
      for (unsigned i = 1; i < _length;i++) {
	result += " | ";
	result += _literals[i].toString();
      }
    }
  }
  return result;
} // SATClause::toString


};

std::ostream& operator<< (std::ostream& out, const SAT::SATClause& cl )
{
  return out<<cl.toString();
}

