
/*
 * File ArithmeticIndex.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ArithmeticIndex.cpp
 * Implements class ArithmeticIndex.
 */

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"

#include "ArithmeticIndex.hpp"

namespace Indexing
{
#if 0
using namespace Kernel;

struct ConstraintDatabase::ConstraintInfo {
  ConstraintInfo() : hasUpperLimit(false), hasLowerLimit(false) {}

  bool hasUpperLimit;
  bool strongUpperLimit;
  InterpretedType upperLimit;
  Clause* upperLimitPremise;

  bool hasLowerLimit;
  bool strongLowerLimit;
  InterpretedType lowerLimit;
  Clause* lowerLimitPremise;

  DHMap<InterpretedType, Clause*> neqConstraints;

  CLASS_NAME(ArithmeticIndex::ConstraintInfo);
  USE_ALLOCATOR(ConstraintInfo);
};


ConstraintDatabase::ConstraintDatabase()
{
  theory=Theory::instance();
}

bool ConstraintDatabase::isNonEqual(TermList t, InterpretedType val, Clause*& premise)
{
  CALL("ConstraintDatabase::isNonEqual");

  ConstraintInfo* ci;
  if(!_termConstraints.find(t, ci)) {
    return false;
  }
  ASS(ci);
  if( ci->hasLowerLimit && (ci->lowerLimit > val ||
      (ci->strongLowerLimit && ci->lowerLimit==val) ) ) {
    premise=ci->lowerLimitPremise;
    return true;
  }
  if( ci->hasUpperLimit && (ci->upperLimit < val ||
      (ci->strongUpperLimit && ci->upperLimit==val) ) ) {
    premise=ci->upperLimitPremise;
    return true;
  }
  Clause* neqPremise;
  if(ci->neqConstraints.find(val, neqPremise)) {
    premise=neqPremise;
    return true;
  }
  return false;
}

bool ConstraintDatabase::isGreater(TermList t, InterpretedType val, Clause*& premise)
{
  CALL("ConstraintDatabase::isGreater");

  ConstraintInfo* ci;
  if(!_termConstraints.find(t, ci)) {
    return false;
  }
  ASS(ci);
  if( ci->hasLowerLimit && (ci->lowerLimit > val ||
      (ci->strongLowerLimit && ci->lowerLimit==val) ) ) {
    premise=ci->lowerLimitPremise;
    return true;
  }
  return false;
}

bool ConstraintDatabase::isLess(TermList t, InterpretedType val, Clause*& premise)
{
  CALL("ConstraintDatabase::isLess");

  ConstraintInfo* ci;
  if(!_termConstraints.find(t, ci)) {
    return false;
  }
  ASS(ci);
  if( ci->hasUpperLimit && (ci->upperLimit > val ||
      (ci->strongUpperLimit && ci->upperLimit==val) ) ) {
    premise=ci->upperLimitPremise;
    return true;
  }
  return false;
}


void ConstraintDatabase::handleLiteral(Literal* lit, bool adding, Clause* premise, bool negative)
{
  CALL("ConstraintDatabase::handleLiteral");

  Signature::Symbol* sym0=env.signature->getPredicate(lit->functor());

  if(lit->arity()!=2 || !sym0->interpreted()) {
    return;
  }
  Signature::InterpretedSymbol* sym=static_cast<Signature::InterpretedSymbol*>(sym0);
  Interpretation itp=sym->getInterpretation();
  if(itp!=Theory::GREATER && itp!=Theory::EQUAL) {
    return;
  }

  TermList arg;
  InterpretedType num;
  bool numFirst=theory->isInterpretedConstant(*lit->nthArgument(0));
  if(numFirst) {
    if(theory->isInterpretedConstant(*lit->nthArgument(1))) {
      //comparison of two interpreted constants is of no use to us
      return;
    }
    num=theory->interpretConstant(*lit->nthArgument(0));
    arg=*lit->nthArgument(1);
  }
  else {
    if(!theory->isInterpretedConstant(*lit->nthArgument(1))) {
      //we don't have a comparison with a number
      return;
    }
    num=theory->interpretConstant(*lit->nthArgument(1));
    arg=*lit->nthArgument(0);
  }

  bool litPositive = static_cast<bool>(lit->polarity()) ^ negative;

  if(itp==Theory::EQUAL) {
    if(litPositive) {
      return;
    }
    if(adding) {
      ConstraintInfo** pctr;
      if(_termConstraints.getValuePtr(arg, pctr)) {
        *pctr=new ConstraintInfo;
      }
      ConstraintInfo* ctr=*pctr;
      //if there is an inequality with this number already, the new one won't be inserted
      ctr->neqConstraints.insert(num, premise);
    }
    else {
      ConstraintInfo* ctr=_termConstraints.get(arg);
      Clause* storedPrem;
      if(ctr->neqConstraints.find(num, storedPrem)) {
        if(storedPrem==premise) {
          ALWAYS(ctr->neqConstraints.remove(num));
        }
      }
    }
    return;
  }


  bool strong = litPositive;
  bool upper = !(numFirst ^ litPositive);

  if(adding) {
    ConstraintInfo** pctr;
    if(_termConstraints.getValuePtr(arg, pctr)) {
      *pctr=new ConstraintInfo;
    }
    ConstraintInfo* ctr=*pctr;
    if(upper) {
      if( !ctr->hasUpperLimit || ctr->upperLimit > num ||
	  (strong && !ctr->strongUpperLimit && ctr->upperLimit==num) ) {
	ctr->hasUpperLimit=true;
	ctr->strongUpperLimit=strong;
	ctr->upperLimit=num;
	ctr->upperLimitPremise=premise;
      }
    }
    else {
      if( !ctr->hasLowerLimit || ctr->lowerLimit < num ||
	  (strong && !ctr->strongLowerLimit && ctr->lowerLimit==num) ) {
	ctr->hasLowerLimit=true;
	ctr->strongLowerLimit=strong;
	ctr->lowerLimit=num;
	ctr->lowerLimitPremise=premise;
      }
    }
  }
  else {
    ConstraintInfo* ctr=_termConstraints.get(arg);
    if(upper) {
      if(premise==ctr->upperLimitPremise) {
	ctr->hasUpperLimit=false;
      }
    }
    else {
      if(premise==ctr->lowerLimitPremise) {
	ctr->hasLowerLimit=false;
      }
    }
  }
}

ArithmeticIndex::ArithmeticIndex()
{
}

void ArithmeticIndex::handleClause(Clause* c, bool adding)
{
  CALL("ArithmeticIndex::handleClause");
//  ASS(env.options->interpretedEvaluation()); //this index should be used only when we interpret symbols

  if(c->length()!=1){
    return;
  }

  Literal* lit=(*c)[0];
  _db.handleLiteral(lit, adding, c);
}
#endif
}
