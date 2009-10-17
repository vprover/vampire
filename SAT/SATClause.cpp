/**
 * @file SATClause.cpp
 * Implements class SATClause.
 */

#include <algorithm>
#include <ostream>

#include "../Lib/Allocator.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Int.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"

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
  CALL("SATClause::operator new");

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
  CALL("SATClause::destroy");

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


SATClauseList* SATClause::fromFOClauses(ClauseIterator clauses)
{
  CALL("SATClause::fromFOClauses/1");

  NamingContext context;
  return fromFOClauses(context, clauses);
}

SATClauseList* SATClause::fromFOClauses(NamingContext& context, ClauseIterator clauses)
{
  CALL("SATClause::fromFOClauses/2");

  SATClauseList* res=0;

  while(clauses.hasNext()) {
    Clause* cl=clauses.next();
    SATClauseList::push(fromFOClause(context,cl), res);
  }

  return res;
}

SATClause* SATClause::fromFOClause(NamingContext& context, Clause* cl)
{
  CALL("SATClause::fromFOClause");

  unsigned clen=cl->length();
  SATClause* rcl=new(clen) SATClause(clen);

  for(unsigned i=0;i<clen;i++) {
    ASS_REP((*cl)[i]->ground(), *(*cl)[i]);
    (*rcl)[i]=litToSAT(context, (*cl)[i]);
  }
  return rcl;
}


SATLiteral SATClause::litToSAT(NamingContext& context, Literal* lit)
{
  CALL("SATClause::litToSAT");

  int num;
  if(context.map.find(lit, num)) {
    return SATLiteral(abs(num), num>0?1:0);
  }
  if(lit->isPositive()) {
    num=context.nextVar++;
    context.map.insert(lit, num);
    return SATLiteral(num, 1);
  }

  Literal* posLit=Literal::oppositeLiteral(lit);
  if(context.map.find(posLit, num)) {
    context.map.insert(lit, -num);
    return SATLiteral(num, 0);
  }

  num=context.nextVar++;

  context.map.insert(posLit, num);
  context.map.insert(lit, -num);
  return SATLiteral(num, 0);
}


/**
 * Convert the clause to the string representation.
 */
string SATClause::toString() const
{
  CALL("SATClause::toString");

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

/**
 * Convert the clause to the DIMACS string representation.
 */
string SATClause::toDIMACSString() const
{
  CALL("SATClause::toDIMACSString");

  string result;
  for(unsigned i=0;i<_length;i++) {
    ASS_G(_literals[i].var(),0);
    if(i!=0) {
      result+=" ";
    }
    if(!_literals[i].polarity()) {
      result+="-";
    }
    result += Int::toString(_literals[i].var());
  }
  result+=" 0";
  return result;
}


};

std::ostream& operator<< (std::ostream& out, const SAT::SATClause& cl )
{
  return out<<cl.toString();
}

