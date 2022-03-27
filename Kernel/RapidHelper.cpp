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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include "Indexing/Index.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/EqHelper.hpp"

#include "Shell/Options.hpp"

#include "RapidHelper.hpp"

namespace Kernel {


bool RapidHelper::isIntegerComparisonLiteral(Literal* lit) {
  CALL("RapidHelper::isIntegerComparisonLiteral");

  if (!theory->isInterpretedPredicate(lit)) return false;
  switch (theory->interpretPredicate(lit)) {
    case Theory::INT_LESS:
      // The only supported integer comparison predicate is INT_LESS.
      break;
    case Theory::INT_LESS_EQUAL:
    case Theory::INT_GREATER_EQUAL:
    case Theory::INT_GREATER:
      // All formulas should be normalized to only use INT_LESS and not other integer comparison predicates.
      ASSERTION_VIOLATION;
    default:
      // Not an integer comparison.
      return false;
  }
  return true;
}

bool RapidHelper::maybeDifferentBounds(Literal* l) {
  CALL("RapidHelper::maybeDifferentBounds");

  if(l->isPositive() && theory->isInterpretedPredicate(l, Theory::INT_LESS)){
    TermList t1 = *l->nthArgument(0);
    TermList t2 = *l->nthArgument(1);
    if(t1.isTerm() && t1.term()->ground() &&
       env.signature->getFunction(t1.term()->functor())->skolem() &&
       t2.isTerm() && t2.term()->ground() &&
       env.signature->getFunction(t2.term()->functor())->skolem() ){
      return true;
    }
  }
  return false;
}

bool RapidHelper::mallocClause(Clause* c) {
  CALL("RapidHelper::mallocClause");

  auto isMallocOrMallocPlusIntConst = [](TermList t, Term*& mallocTerm) {
    if(t.isVar()){ return false; }
    Term* tt = t.term();
    if(env.signature->getFunction(tt->functor())->malloc()){
      mallocTerm = tt;
      return true;
    }

    if(theory->isInterpretedFunction(t, Theory::INT_PLUS)){
      TermList t1 = *tt->nthArgument(0);
      TermList t2 = *tt->nthArgument(1);
      IntegerConstantType a;
      if ( theory->tryInterpretConstant(t1, a) && t2.isTerm() &&
           env.signature->getFunction(t2.term()->functor())->malloc()) {
        mallocTerm = t2.term();
        return true;
      }

      if ( theory->tryInterpretConstant(t2, a) && t1.isTerm() &&
           env.signature->getFunction(t1.term()->functor())->malloc()) {
        mallocTerm = t1.term();
        return true;
      }
    }

    return false;
  };

  if(c->length() != 2){ return false; }
  Literal* l1 = (*c)[0];
  Literal* l2 = (*c)[1];
  Literal* equalityLit;
  Literal* mallocLit;

  if(l1->isTwoVarEquality() && l1->isPositive() &&
     *l1->nthArgument(0) != *l1->nthArgument(1) ){
    equalityLit = l1;
    mallocLit = l2;
  } else if(l2->isTwoVarEquality() && l2->isPositive() &&
           *l2->nthArgument(0) != *l2->nthArgument(1)){
    equalityLit = l2;
    mallocLit = l1;
  } else {
    // neither literal of the form X = Y
    return false;
  }

  if(!mallocLit->isEquality() || mallocLit->isPositive()){
    return false;
  }

  TermList x = *equalityLit->nthArgument(0);
  TermList y = *equalityLit->nthArgument(1);

  TermList t1 = *mallocLit->nthArgument(0);
  TermList t2 = *mallocLit->nthArgument(1);
  Term* malloct1 =0;
  Term* malloct2 =0;
  if(isMallocOrMallocPlusIntConst(t1, malloct1) && isMallocOrMallocPlusIntConst(t2, malloct2)){
    ASS(malloct1 && malloct2);
    TermList tp1 = *malloct1->nthArgument(0);
    TermList tp2 = *malloct2->nthArgument(0);

    if(tp1.isVar() || tp2.isVar()){ return false; }
    Term* tp1t = tp1.term();
    Term* tp2t = tp2.term();

    auto fun = env.signature->getFunction(tp1t->functor());
    if(!fun->timePoint() || 
       tp1t->functor() != tp2t->functor() || !tp1t->arity()){
      // not the same timepoint or not a timepoint within a loop
      return false;
    }

    bool pairFound = false;
    DHSet<TermList>  varArgs;
    for(unsigned i = 0; i < tp1t->arity(); i++){
      TermList arg1 = *tp1t->nthArgument(i);
      TermList arg2 = *tp2t->nthArgument(i);
      if(!arg1.isVar() || !arg2.isVar() || arg1 == arg2){
        return false;
      }
      if(!varArgs.insert(arg1) || !varArgs.insert(arg2)){
        return false;
      }
      if((arg1 ==  x && arg2 == y) || (arg1 ==  y && arg2 == x)){
        pairFound = true;
      }
    }
    return pairFound;
  }

  return false;

}


bool RapidHelper::isDensityLiteral(Literal* l, unsigned& varFunctor, unsigned& tpFunctor)
{
  CALL("RapidHelper::isDensityLiteral");

  if(l->arity()){
    return false;
  }

  vstring name = env.signature->getPredicate(l->functor())->name();
  if(name.find("Dense") == vstring::npos){
    return false;
  }

  unsigned posOfFirstDash = 6;
  unsigned posOfSecondDash = name.find('-', 7);
 
  vstring programVarName = name.substr(posOfFirstDash + 1, posOfSecondDash - posOfFirstDash - 1);
  vstring timePoint = name.substr(posOfSecondDash + 1, name.length() - posOfSecondDash - 2);

  varFunctor = env.signature->getFunctionNumber(programVarName, 1);
  //very dangerous! the timepoint can take multiple loop counters, so may
  //not have arity 1!
  tpFunctor = env.signature->getFunctionNumber(timePoint, 1);
  return true;
}

bool RapidHelper::isSuitableForInduction(Literal* lit, vstring& tpName)
{
  CALL("RapidHelper::isSuitableForInduction");

  auto isProgramVarAtSkolem = [&tpName](TermList t) {
    if(t.isTerm()){
      Term* tTerm = t.term();
      if(env.signature->getFunction(tTerm->functor())->programVar()){
        TermList timePoint = *tTerm->nthArgument(0);
        if(timePoint.isTerm() && timePoint.term()->arity()){
          Term* tp = timePoint.term();
          tpName = env.signature->getFunction(tp->functor())->name();
          TermList iter = *tp->nthArgument(tp->arity() - 1);
          if(iter.isTerm()){
            Term* iTerm = iter.term();
            if(env.signature->getFunction(iTerm->functor())->inductionSkolem()){
              return true;
            }
          }
        }
      }
    }
    return false;
  };
  
  if(isIntegerComparisonLiteral(lit)){
    TermList arg1 = *lit->nthArgument(0);
    TermList arg2 = *lit->nthArgument(1);

    IntegerConstantType a;
    if ( theory->tryInterpretConstant(arg1, a)) {
      if(isProgramVarAtSkolem(arg2)){
        return true;
      }
    }

    if ( theory->tryInterpretConstant(arg2, a)) {
      if(isProgramVarAtSkolem(arg1)){
        return true;
      }
    }

    if (isProgramVarAtSkolem(arg1) && isProgramVarAtSkolem(arg2)) {
      return true;
    }    
  }
  return false;
}

bool RapidHelper::isRightLimitLiteral(Literal* l) {
  CALL("RapidHelper::isLimitLiteral");

  //only interested in <
  if(!isIntegerComparisonLiteral(l) || !l->polarity()){
    return false;
  }

  TermList rhs = *l->nthArgument(1);
  if(rhs.isVar()){
    return false;
  }

  Term* t = rhs.term();
  if(t->arity() != 1){
    return false;
  }

  TermList timePoint = *t->nthArgument(0);
  if(timePoint.isVar()){
    return false;
  }

  Term* tp = timePoint.term();
  unsigned f = tp->functor();
  if(!env.signature->getFunction(f)->timePoint()){
    //not actually a timepoint
    return false;
  }

  if(tp->arity() != 1){
    //either of the form l# or of the form l(nl#, nl#,...)
    //for now we ignore the nested loop case
    return false;
  }

  TermList lastLoopCount = *tp->nthArgument(0);
 
  if(lastLoopCount.isVar()){
    return false;
  }

  f = lastLoopCount.term()->functor();
  if(!env.signature->getFunction(f)->finalLoopCount()){
    return false;
  }

  return true;
}
 
bool RapidHelper::isArrayAccessLit(Literal* lit, TermList& itVar, 
  unsigned& side, TermStack& arrayAccessesRHS) {
  CALL("RapidHelper::isArrayAccessLit");

  auto isArrayAtNextIt = [&itVar](TermList t) {
    //return true if t is 1 of $uminus(1)
    if(t.isTerm() && t.term()->arity() ==2 ){
      TermList t1 = *t.term()->nthArgument(0);
      TermList t2 = *t.term()->nthArgument(1);
      if(t2.isTerm() && t2.term()->arity() == 1){
        TermList t3 = *t2.term()->nthArgument(0);
        if(isTimePointAtNextIter(t1, t3, itVar)){
          return true;
        }
      }
    }
    return false;
  };

  if(!lit->isEquality()){
    return false;
  }

  TermList arr, index, indexAtNextIt, rhs;
  if(isArrayAtNextIt(*lit->nthArgument(0))){
    side = 0;
    arr = *lit->nthArgument(0);
    rhs = *lit->nthArgument(1);
  } else if (isArrayAtNextIt(*lit->nthArgument(1))) {
    side = 1;
    arr = *lit->nthArgument(1);
    rhs = *lit->nthArgument(0);    
  } else {
    return false;
  }

  index = *arr.term()->nthArgument(1);
  indexAtNextIt = intVarAtNextIt(index);

  ASS(rhs.isTerm());
  NonVariableIterator sit(rhs.term(), true);
  while(sit.hasNext()) {
    TermList terml = sit.next();
    if(terml.isTerm()){
      Term* term = terml.term();
      if(env.signature->getFunction(term->functor())->programVar() &&
        term->functor() != arr.term()->functor()
         && terml != index && terml != indexAtNextIt){
        return false;
      }
      if(term->functor() == arr.term()->functor()){
        arrayAccessesRHS.push(terml);
      }
    }
  }

  return true; //rhs.containsSubterm(arrAtPrevIt(lhs));
}

bool RapidHelper::isSubLiteral(Literal* l, TermList& itVar) {
  CALL("RapidHelper::isSubLiteral");

  auto natTA = env.signature->getNat();

  if(l->functor() == natTA->getLessPredicate()){
    if(!l->polarity()){

      TermList t1 = *l->nthArgument(0);
      TermList t2 = *l->nthArgument(1);
      if(t1.isVar() && isFinalLoopCount(t2)){
        itVar = t1;
        return true;
      }
    }
  }

  return false;
}

bool RapidHelper::isStrongDensityClause(Clause* c, unsigned& litPos, 
  unsigned& termPos) {
  CALL("RapidHelper::isStrongDensityClause");

  if(c->length() != 2){
    return false;
  }

  TermList var1, var2;
  if(isStrongDensityLiteral((*c)[0], var1, termPos) && 
     isSubLiteral((*c)[1], var2) &&
     var1 == var2){
     litPos = 0;
     return true;
  }

  if(isSubLiteral((*c)[0], var1) && 
     isStrongDensityLiteral((*c)[1], var2, termPos) &&
     var1 == var2){
     litPos = 1;
     return true;    
  }

  return false;
}

bool RapidHelper::isArrayAccessClause(Clause* c, unsigned& litPos, 
  unsigned& termPos, TermStack& arrayAccessesRHS) {
  CALL("RapidHelper::isStrongDensityClause");

  if(c->length() != 2){
    return false;
  }

  TermList var1, var2;
  if(isArrayAccessLit((*c)[0], var1, termPos, arrayAccessesRHS) && 
     isSubLiteral((*c)[1], var2) &&
     var1 == var2){
     litPos = 0;
     return true;
  } 
  arrayAccessesRHS.reset();
  
  if(isSubLiteral((*c)[0], var1) && 
     isArrayAccessLit((*c)[1], var2, termPos, arrayAccessesRHS) &&
     var1 == var2){
     litPos = 1;
     return true;
  } 

  return false;
}

bool RapidHelper::isTimePointAtNextIter(TermList t1, TermList t2, TermList& itVar) {
  CALL("RapidHelper::isTimePointAtNextIter");

  if(isTimePoint(t1) && isTimePoint(t2) && 
     t1.term()->functor() == t2.term()->functor()){
   

    auto natTA = env.signature->getNat();

    unsigned arity = t1.term()->arity();

    for(unsigned i = 0; i < arity; i++){
      TermList tl1 = *t1.term()->nthArgument(i);
      TermList tl2 = *t2.term()->nthArgument(i);

      if(tl2.isTerm()){
        return false;
      }
      if((tl1 != tl2 && i < arity - 1) ||
         (tl1 != natTA->createSucc(tl2) && i == (arity - 1))){
        return false;
      }
    }
    
    itVar = *t2.term()->nthArgument(arity - 1);
    return true;
  }
  return false;
}


bool RapidHelper::isStrongDensityLiteral(Literal* lit, TermList& itVar, 
  unsigned& side) {
  CALL("RapidHelper::isStrongDensityLiteral");

  auto isOneOrMinusOne = [](TermList t) {
    //return true if t is 1 of $uminus(1)
    IntegerConstantType it;
    if(theory->tryInterpretConstant(t,it) && it.toInner() == 1){ 
      return true; 
    }

    if(theory->isInterpretedFunction(t, Theory::INT_UNARY_MINUS)){
      if(theory->tryInterpretConstant(*t.term()->nthArgument(0),it) 
          && it.toInner() == 1){ 
        return true; 
      }    
    }

    return false;
  };

  auto isVarAtNextIteration = [&itVar](TermList t1, TermList t2) {
    //return true if t1 is x(l#(It1 .... s(Itn))) and
    //t2 is x(l#(It1 .... Itn))

    if(t1.isTerm() && t2.isTerm() && 
       t1.term()->functor() == t2.term()->functor() &&
       t1.term()->arity() == 1){
       t1 = *t1.term()->nthArgument(0);
       t2 = *t2.term()->nthArgument(0);
       return isTimePointAtNextIter(t1, t2, itVar);
    }
  
    return false;
  };

  if(!lit->isEquality()){
    return false;
  }

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);

  //some easy rejections
  if(lhs.isVar() || rhs.isVar() || !lhs.term()->arity() || 
    !rhs.term()->arity() || 
    (!theory->isInterpretedFunction(lhs, Theory::INT_PLUS)  && 
     !theory->isInterpretedFunction(rhs, Theory::INT_PLUS))) {
    return false;
  }

  Term* lhsTerm = lhs.term();
  Term* rhsTerm = rhs.term();
  Term* l;
  Term* r;
  if(!((lhsTerm->arity() == 1 && rhsTerm->arity() == 2) ||
       (lhsTerm->arity() == 2 && rhsTerm->arity() == 1))){
    return false;
  } else if(lhsTerm->arity() == 1){
    side = 0;
    l = lhsTerm;
    r = rhsTerm;
  } else {
    side = 1;
    l = rhsTerm;
    r = lhsTerm;
  }
  ASS(l->arity() == 1 && r->arity() == 2);

  TermList arg1 = *r->nthArgument(0);
  TermList arg2 = *r->nthArgument(1);

  if(!isOneOrMinusOne(arg1) && !isOneOrMinusOne(arg2)){
    return false;
  }

  if(!isVarAtNextIteration(TermList(l),arg1) && 
     !isVarAtNextIteration(TermList(l),arg2)){
    return false;
  }
 
  return true;
}

TermList RapidHelper::replaceFinalArg(Term* t, TermList replacement) {
  CALL("RapidHelper::replaceFinalArg");

  TermStack args;
  for(unsigned i = 0; i < t->arity(); i++){
    if(i < t->arity() - 1){
      args.push((*t)[i]);
    } else {
      args.push(replacement);
    }
  }
  return TermList(Term::create(t,args.begin()));
}


TermList RapidHelper::timePointAtNextIt(TermList tp) {
  CALL("RapidHelper::timePointAtNextIt");
  ASS(tp.isTerm());
  ASS(env.signature->getFunction(tp.term()->functor())->timePoint());

  auto natTA = env.signature->getNat();
  ASS(natTA);

  Term* tpTerm = tp.term();
  unsigned arity = tpTerm->arity();
  TermList succTerm = natTA->createSucc((*tpTerm)[arity -1]);
  return replaceFinalArg(tpTerm, succTerm);
}

TermList RapidHelper::timePointAtPrevIt(TermList tp) {
  CALL("RapidHelper::timePointAtPrevIt");
  ASS(tp.isTerm());
  ASS(env.signature->getFunction(tp.term()->functor())->timePoint());

  Term* tpTerm = tp.term();
  unsigned arity = tpTerm->arity();

  TermList succTerm = (*tpTerm)[arity -1];
  ASS(succTerm.isTerm() && succTerm.term()->arity());
  return replaceFinalArg(tpTerm, (*succTerm.term())[0]);
}

TermList RapidHelper::timePointAtFirstIt(TermList tp) {
  CALL("RapidHelper::timePointAtFirstIt");
  ASS(tp.isTerm());
  ASS(env.signature->getFunction(tp.term()->functor())->timePoint());

  auto natTA = env.signature->getNat();
  ASS(natTA);
  TermList zero = natTA->createZero();
  return replaceFinalArg(tp.term(), zero);
}

TermList RapidHelper::timePointAtLastIt(TermList tp, TermList finalLoopCount) {
  CALL("RapidHelper::timePointAtLastIt");
  ASS(tp.isTerm());
  ASS(env.signature->getFunction(tp.term()->functor())->timePoint());

  return replaceFinalArg(tp.term(), finalLoopCount);
}

TermList RapidHelper::intVarAtNextIt(TermList varTerm) {
  CALL("RapidHelper::intVarAtNextIt");

  ASS(varTerm.isTerm() && varTerm.term()->arity() == 1);
  TermList tpTerm = *varTerm.term()->nthArgument(0);
  TermList tpTermNextIt = timePointAtNextIt(tpTerm);
  return TermList(Term::create1(varTerm.term()->functor(), tpTermNextIt));
}

TermList RapidHelper::intVarAtFirstIt(TermList varTerm) {
  CALL("RapidHelper::intVarAtFirstIt");

  ASS(varTerm.isTerm() && varTerm.term()->arity() == 1);
  TermList tpTerm = *varTerm.term()->nthArgument(0);
  TermList tpTermFirstIt = timePointAtFirstIt(tpTerm);
  return TermList(Term::create1(varTerm.term()->functor(), tpTermFirstIt));
}

TermList RapidHelper::intVarAtLastIt(TermList varTerm, TermList finalLoopCount) {
  CALL("RapidHelper::intVarAtLastIt");

  ASS(varTerm.isTerm() && varTerm.term()->arity() == 1);
  TermList tpTerm = *varTerm.term()->nthArgument(0);
  TermList tpTermLastIt = timePointAtLastIt(tpTerm, finalLoopCount);
  return TermList(Term::create1(varTerm.term()->functor(), tpTermLastIt));
}  

TermList RapidHelper::arrAtPrevIt(TermList arrVarTerm) {
  CALL("RapidHelper::arrAtPrevIt");
  ASS(arrVarTerm.isTerm() && arrVarTerm.term()->arity() == 2);

  Term* arrVar = arrVarTerm.term();
  TermList tpTerm = (*arrVar)[0];
  TermList index = (*arrVar)[1];
  TermList tpTermPrevIt = timePointAtPrevIt(tpTerm);
  return TermList(Term::create2(arrVar->functor(), tpTermPrevIt, index));
}

TermList RapidHelper::arrAtFirstIt(TermList arrVarTerm) {
  CALL("RapidHelper::arrAtFirstIt");
  ASS(arrVarTerm.isTerm() && arrVarTerm.term()->arity() == 2);

  Term* arrVar = arrVarTerm.term();
  TermList tpTerm = (*arrVar)[0];
  TermList index = (*arrVar)[1];
  TermList tpTermFirstIt = timePointAtFirstIt(tpTerm);
  return TermList(Term::create2(arrVar->functor(), tpTermFirstIt, index));
}

TermList RapidHelper::arrAtLastIt(TermList arrVarTerm, TermList finalLoopCount) {
  CALL("RapidHelper::arrAtLastIt");
  ASS(arrVarTerm.isTerm() && arrVarTerm.term()->arity() == 2);

  Term* arrVar = arrVarTerm.term();
  TermList tpTerm = (*arrVar)[0];
  TermList index = (*arrVar)[1];
  TermList tpTermLastIt = timePointAtLastIt(tpTerm, finalLoopCount);
  return TermList(Term::create2(arrVar->functor(), tpTermLastIt, index));
}

TermList RapidHelper::changeArrIndex(TermList arr, TermList newIndex) {
  CALL("RapidHelper::changeArrIndex");
  ASS(arr.isTerm() && arr.term()->arity() == 2);

  Term* arrTerm = arr.term();
  TermList tpTerm = (*arrTerm)[0];
  return TermList(Term::create2(arrTerm->functor(), tpTerm, newIndex));
}


bool RapidHelper::increasing(Literal* lit, TermList term) {
  CALL("RapidHelper::increasing");
  ASS(lit->isEquality());

#if VDEBUG
  TermList var;
  unsigned termPos;
  ASS(isStrongDensityLiteral(lit, var, termPos));
#endif

  TermList otherSide = EqHelper::getOtherEqualitySide(lit, term);
  ASS(otherSide.isTerm());
  TermList intConst = *otherSide.term()->nthArgument(1);
  if(theory->isInterpretedFunction(intConst, Theory::INT_UNARY_MINUS)){
    return false;
  }
  return true;
}

TermList RapidHelper::getFinalCountFromSubLit(Literal* lit) {
  CALL("RapidHelper::getFinalCountFromSubLit");
  ASS(lit->arity() == 2);

#if VDEBUG
  TermList var;
  ASS(isSubLiteral(lit, var));
#endif  

  return *lit->nthArgument(1);
}



bool RapidHelper::isLeftLimitLiteral(Literal* l) {
  CALL("RapidHelper::isLimitLiteral");

  //only interested in >=
  if(!isIntegerComparisonLiteral(l) || l->polarity()){
    return false;
  }

  TermList rhs = *l->nthArgument(1);
  if(rhs.isVar()){
    return false;
  }

  Term* t = rhs.term();

  if(env.signature->getFunction(t->functor())->integerConstant()){
    return true;
  }

  if(t->arity() != 1){
    return false;
  }

  TermList timePoint = *t->nthArgument(0);
  if(timePoint.isVar()){
    return false;
  }

  Term* tp = timePoint.term();
  unsigned f = tp->functor();
  if(!env.signature->getFunction(f)->timePoint()){
    //not actually a timepoint
    return false;
  }

  if(tp->arity() != 1){
    //either of the form l# or of the form l(nl#, nl#,...)
    //for now we ignore the nested loop case
    return false;
  }

  TermList zero = *tp->nthArgument(0);
 
  if(zero.isVar()){
    return false;
  }

  //TODO update to the non-nat case 
  auto natTA = env.signature->getNat();
  if(natTA){
    if(zero != natTA->createZero()){
      return false;
    }
  }

  return true;
}

bool RapidHelper::isFinalLoopCount(TermList t)
{
  CALL("RapidHelper::isFinalLoopCount");

  if(!t.isTerm()) return false;
  return env.signature->getFunction(t.term()->functor())->finalLoopCount();
}

bool RapidHelper::isTimePoint(TermList t){
  CALL("RapidHelper::isTimePoint");

  if(t.isVar()){ return false; }
  return env.signature->getFunction(t.term()->functor())->timePoint();
}

}  // namespace Inferences
