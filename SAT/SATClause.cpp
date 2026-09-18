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

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"

#include "Shell/Statistics.hpp"

#include "SATInference.hpp"

#include "SATClause.hpp"


namespace SAT {

using namespace Lib;
using namespace Shell;

unsigned SATClause::_lastNumber = 0;

/**
 * Allocate a clause having lits literals.
 */
void* SATClause::operator new(size_t sz,unsigned lits)
{
  return ALLOC_KNOWN(allocationRequired(lits),"SATClause");
}

void SATClause::operator delete(void *ptr, size_t sz) {
  SATClause *self = static_cast<SATClause *>(ptr);
  unsigned lits = self->length();
  DEALLOC_KNOWN(ptr, allocationRequired(lits), "SATClause");
}

SATClause::SATClause(unsigned length)
  : number(++_lastNumber), _length(length), _nonDestroyable(0), _inference(0)
{
  env.statistics->satClauses++;
  if(length==1) {
    env.statistics->unitSatClauses++;
  }
  else if(length==2) {
    env.statistics->binarySatClauses++;
  }

  // call a constructor on the literals
  for (size_t i = 0; i < _length; i++)
    ::new (&literals()[i]) SATLiteral();
}

/**
 * Destroy the SATClause object.
 */
void SATClause::destroy()
{
  if(_nonDestroyable) {
    //we don't destroy non-destroyable clauses.
    //This is to protect clauses which may act as premises to other clauses.
    return;
  }

  if(_inference) {
    delete _inference;
  }

  unsigned lits = _length;
  // call a destructor on the excess literals
  for (size_t i = 0; i < lits; i++)
    literals()[i].~SATLiteral();

  // call a destructor of the clause object
  this->~SATClause();

  DEALLOC_KNOWN(this, allocationRequired(lits),"SATClause");
} // SATClause::destroy


void SATClause::setInference(SATInference* val)
{
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

void SATClause::sort()
{
  std::sort(literals(), literals() + length(), [](SATLiteral l, SATLiteral k) -> bool {
    return l.var() < k.var() || (l.var() == k.var() && l.positive() < k.positive());
  });
}

SATClause* SATClause::removeDuplicateLiterals(SATClause* cl)
{
  unsigned clen=cl->length();

  cl->sort();

  unsigned duplicate=0;
  for(unsigned i=1;i<clen;i++) {
    if((*cl)[i-1].var()==(*cl)[i].var()) {
      if((*cl)[i-1].positive()==(*cl)[i].positive()) {
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
    SATClause* cl2=new(newLen) SATClause(newLen);

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

std::ostream &operator<<(std::ostream &out, const SATClause &cl)
{
  out << "s" << cl.number << ". ";
  if (cl.length() == 0)
    out << "#";
  else {
    out << cl[0];
    for(unsigned i = 1; i < cl.length(); i++)
      out << " | " << cl[i];
  }

  SATInference *inference = cl.inference();
  if(!inference)
    return out;

  bool first = true;
  out << " [";
  switch(inference->getType()) {
    case SATInference::PROP_INF: {
      out << "rat ";
      PropInference *deduction = static_cast<PropInference *>(inference);
      for(SATClause *premise : iterTraits(deduction->getPremises()->iter())) {
        if(!first)
          out << ",";
        first = false;
        out << "s" << premise->number;
      }
      break;
    }
    case SAT::SATInference::FO_CONVERSION: {
      FOConversionInference *deduction = static_cast<FOConversionInference *>(inference);
      out << "sat_conversion " << deduction->getOrigin()->number();
      break;
    }
  }
  return out << "]";
}

};
