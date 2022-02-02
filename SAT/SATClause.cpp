/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file SATClause.cpp
 * Implements class SATClause.
 */

#include <algorithm>
#include <ostream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"

#include "SATInference.hpp"

#include "SATClause.hpp"


namespace SAT {

using namespace Lib;
using namespace Shell;

/**
 * Allocate a clause having lits literals.
 */
void* SATClause::operator new(size_t sz,unsigned lits)
{
  CALL("SATClause::operator new");

  //We have to get sizeof(SATClause) + (_length-1)*sizeof(SATLiteral*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sz+lits*sizeof(SATLiteral);
  /*
    it's not safe to save memory for the empty clause,
    since the compiler wants to call a constructor 
    on the only officially declared literal, see:
  
    SATLiteral _literals[1];
  */
  if (lits > 0)
    size-=sizeof(SATLiteral);

  return ALLOC_KNOWN(size,"SATClause");
}

SATClause::SATClause(unsigned length,bool kept)
  : _activity(0), _length(length), _kept(kept?1:0), _nonDestroyable(0), _inference(0)
//      , _genCounter(0xFFFFFFFF)
{
  env.statistics->satClauses++;
  if(length==1) {
    env.statistics->unitSatClauses++;
  }
  else if(length==2) {
    env.statistics->binarySatClauses++;
  }

  // call a constructor on the literals
  for (size_t i = 1; i < _length; i++)
    new (&_literals[i]) SATLiteral();
}

/**
 * Destroy the SATClause object.
 */
void SATClause::destroy()
{
  CALL("SATClause::destroy");

  if(_nonDestroyable) {
    //we don't destroy non-destroyable clauses.
    //This is to protect clauses which may act as premises to other clauses.
    return;
  }

  if(_inference) {
    delete _inference;
  }
  
  //We have to get sizeof(SATClause) + (_length-1)*sizeof(SATLiteral*)
  //this way, because _length-1 wouldn't behave well for
  //_length==0 on x64 platform.
  size_t size=sizeof(SATClause)+_length*sizeof(SATLiteral);
  if (_length > 0) // see comment in operator new(size_t sz,unsigned lits) above
    size-=sizeof(SATLiteral);

  // call a destructor on the excess literals
  for (size_t i = 1; i < _length; i++)
    _literals[i].~SATLiteral();    
  
  // call a destructor of the clause object (will destroy _literals[0])
  this->~SATClause();
    
  DEALLOC_KNOWN(this, size,"SATClause");
} // SATClause::destroy


void SATClause::setInference(SATInference* val)
{
  CALL("SATClause::setInference");
  ASS(!_inference);

  _inference = val;
  if(_inference->getType()==SATInference::PROP_INF) {
    SATClauseList* premises = static_cast<PropInference*>(val)->getPremises();
    SATClauseList::Iterator pit(premises);
    while(pit.hasNext()) {
      SATClause* prem = pit.next();
      prem->_nonDestroyable = 1;
    }
  }
}


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

bool SATClause::hasUniqueVariables() const
{
  CALL("SATClause::hasUniqueVariables");

  static DHSet<int> seen;
  seen.reset();
  unsigned clen=length();
  for(unsigned i=0; i<clen; i++) {
    if(!seen.insert((*this)[i].var())) {
      return false;
    }
  }
  return true;
}

SATClause* SATClause::removeDuplicateLiterals(SATClause* cl)
{
  CALL("SATClause::removeDuplicateLiterals(SATClause*)");

  unsigned clen=cl->length();

  cl->sort();

  unsigned duplicate=0;
  for(unsigned i=1;i<clen;i++) {
    if((*cl)[i-1].var()==(*cl)[i].var()) {
      if((*cl)[i-1].polarity()==(*cl)[i].polarity()) {
        //We must get rid of the first occurrence of the duplicate (at i-1). Removing
        //the second would make us miss the case when there are three duplicates.
        std::swap((*cl)[duplicate], (*cl)[i-1]);
        duplicate++;
      } else {
        //delete tautology clauses
        cl->destroy();
        return 0;
      }
    }
  }
  if(duplicate) {
    unsigned newLen=clen-duplicate;
    SATClause* cl2=new(newLen) SATClause(newLen, true);

    for(unsigned i=0;i<newLen;i++) {
      (*cl2)[i]=(*cl)[duplicate+i];
    }
    cl2->sort();
    if(cl->inference()) {
      SATInference* cl2Inf = new PropInference(cl);
      cl2->setInference(cl2Inf);
    }
    else {
      cl->destroy();
    }
    cl=cl2;
  }
  return cl;
}



SATClause* SATClause::fromStack(SATLiteralStack& stack)
{
  CALL("SATClause::fromStack");

  unsigned clen = stack.size();
  SATClause* rcl=new(clen) SATClause(clen);

  SATLiteralStack::BottomFirstIterator it(stack);

  unsigned i=0;
  while(it.hasNext()) {
    (*rcl)[i]=it.next();
    i++;
  }
  ASS_EQ(i, clen);
  return rcl;
}

SATClause* SATClause::copy(SATClause* cl)
{
  CALL("SATClause::copy");

  unsigned clen = cl->size();
  SATClause* rcl=new(clen) SATClause(clen);

  for(unsigned i=0; i<clen; i++) {
    (*rcl)[i] = (*cl)[i];
  }

  if(cl->inference()) {
    rcl->setInference(SATInference::copy(cl->inference()));
  }

  return rcl;
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

  Literal* posLit=Literal::complementaryLiteral(lit);
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
vstring SATClause::toString() const
{
  CALL("SATClause::toString");

  vstring result;
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
vstring SATClause::toDIMACSString() const
{
  CALL("SATClause::toDIMACSString");

  if(_length==0) {
    return "0";
  }

  vstring result;
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

std::ostream& operator<< (std::ostream& out, const SAT::SATClause& cl )
{
  return out<<cl.toString();
}

};


