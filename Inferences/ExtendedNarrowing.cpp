
/*
 * File ExtendedNarrowing.cpp.
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
 * @file ExtendedNarrowing.cpp
 * Implements class ExtendedNarrowing.
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Substitution.hpp"

#include "Shell/LambdaElimination.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/VirtualIterator.hpp"

#include "ExtendedNarrowing.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void ExtendedNarrowing::attach(SaturationAlgorithm* salg)
{
  CALL("ExtendedNarrowing::attach");

  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<ExtendedNarrowingIndex*> (
	  _salg->getIndexManager()->request(EXTENDED_NARROWING_INDEX) );
}

void ExtendedNarrowing::detach()
{
  CALL("ExtendedNarrowing::detach");

  _index=0;
  _salg->getIndexManager()->release(EXTENDED_NARROWING_INDEX);
  GeneratingInferenceEngine::detach();
}

struct ExtendedNarrowing::IsNarrowableBoolEquality
{
  DECL_RETURN_TYPE(bool);
  bool operator()(Literal* l)
  { 
    if(!l->isEquality()){
      return false;
    }
    
    if(!(SortHelper::getEqualityArgumentSort(l) == Sorts::SRT_BOOL)){
      return false;
    }
    
    TermList lhs = *(l->nthArgument(0));
    TermList rhs = *(l->nthArgument(1));
    
    TermList lhsHead = HOSortHelper::getHead(lhs);
    TermList rhsHead = HOSortHelper::getHead(rhs);
    
    int lhsBoolValue = value(lhs);
    int rhsBoolValue = value(rhs);
     
    if((lhsHead.isVar() && rhsBoolValue > -1) ||
       (rhsHead.isVar() && lhsBoolValue > -1)){
      return true; 
    }
    return false; 
  }
};

struct ExtendedNarrowing::NarrowingResultIterator
{    
   const int QUERY = 0;
   const int RESULT = 1;
   
   typedef Signature::Symbol SS;

   NarrowingResultIterator(Clause* cl, Literal* rwLit, unsigned rwSide, 
                           TermList rwRuleLHS, ResultSubstitutionSP subst): 
   _rwRuleLHS(rwRuleLHS), _rwLit(rwLit), _cl(cl),  _subst(subst)
   { 
  
     //cout << "The rwRuleLHS is " + rwRuleLHS.toString() << endl;
  
     TermList boolVal = *(rwLit->nthArgument(!rwSide));
     int bv = value(boolVal);
     _pol = (bv == rwLit->polarity()); 
   
     TermList t = HOSortHelper::getHead(rwRuleLHS);
     SS* s = env.signature->getFunction(t.term()->functor());
     _const = s->getConst();
   
     _returnedSoFar = 0;
     
     if((_const == SS::AND && !_pol) || 
        (_const == SS::OR  && _pol)  ||
        (_const == SS::IMP && _pol)  ||
        (_const == SS::NOT)){
          _toBeReturned = 1;
        } else {
          _toBeReturned = 2;
        }
   }

   DECL_ELEMENT_TYPE(Clause*);
   
   bool hasNext(){
     CALL("ExtendedNarrowing::NarrowingResultIterator::hasNext");
     return _returnedSoFar < _toBeReturned;
   }
   
   OWN_ELEMENT_TYPE next(){
     CALL("ExtendedNarrowing::NarrowingResultIterator::next");
     
     TermList var1;
     TermList var2;
     
     Literal* l1;
     Literal* l2;
     
     bool addTwoLits = (_const == SS::AND && !_pol) || 
                       (_const == SS::OR  &&  _pol) ||
                       (_const == SS::IMP &&  _pol);
     

     if(_const != SS::NOT){
       var1 = HOSortHelper::getNthArg(_rwRuleLHS,0);
       var2 = HOSortHelper::getNthArg(_rwRuleLHS,1);
       
       TermList var1S = _subst->apply(var1, RESULT);
       TermList var2S = _subst->apply(var2, RESULT);
  
       //cout << "var1: " + var1.toString() + " substituted to " + var1S.toString() << endl;
       //cout << "var2: " + var2.toString() + " substituted to " + var2S.toString() << endl;
  
       if(addTwoLits){
         switch(_const){
          case SS::AND : {
            l1 = toFalsity(var1S);
            l2 = toFalsity(var2S);
            break;
          } 
          case SS::OR : {
            l1 = toTruth(var1S);
            l2 = toTruth(var2S);
            break;            
          }
          case SS::IMP : {
            l1 = toFalsity(var1S);
            l2 = toTruth(var2S);
            break;      
          }
          default:
            ASSERTION_VIOLATION;
         }
       } else {
         if(_const == SS::AND && !_returnedSoFar){
           l1 = toTruth(var1S);
         } else if(_const == SS::AND && _returnedSoFar) {
           l1 = toTruth(var2S);           
         } else if(_const == SS::OR && !_returnedSoFar) {
           l1 = toFalsity(var1S);           
         } else if(_const == SS::OR && _returnedSoFar) {
           l1 = toFalsity(var2S);            
         } else if(_const == SS::IMP && !_returnedSoFar) {
           l1 = toTruth(var1S);           
         } else if(_const == SS::IMP && _returnedSoFar) {
           l1 = toFalsity(var2S);           
         }          
       }
     } else {
       var1 = HOSortHelper::getNthArg(_rwRuleLHS,0);   
       TermList var1S = _subst->apply(var1, RESULT);
       l1 = (_pol ? toFalsity(var1S) : toTruth(var1S));
     }
     
     unsigned cLen = _cl->length();
     unsigned newLen = cLen + addTwoLits; 
     
     Inference* inf = new Inference1(Inference::EXTENDED_NARROWING, _cl); 
     Clause* res = new(newLen) Clause(newLen, _cl->inputType(), inf);

     (*res)[0]=l1;
     if(l2){
       (*res)[1]=l2;  
     }
     
     unsigned next = 1 + addTwoLits;
     for(unsigned i=0;i<cLen;i++) {
       Literal* curr=(*_cl)[i];
       if(curr!=_rwLit) {
         Literal* currAfter = _subst->apply(curr, QUERY);
         (*res)[next++] = currAfter;
       }
     }
     ASS_EQ(next,newLen);

     res->setAge(_cl->age()+1);
     env.statistics->extendedNarrows++;

     _returnedSoFar++;

     //cout << "Narrowing " + _cl->toString() << endl;
     //cout << "Returning " + res->toString() << endl;
     return res;
   }
   
private:
   unsigned _toBeReturned;
   unsigned _returnedSoFar;
   SS::HOLConstant _const;
   bool _pol;
   TermList _rwRuleLHS;
   Literal* _rwLit;
   Clause* _cl;
   ResultSubstitutionSP _subst;
};

struct ExtendedNarrowing::PSNarrowingResultIterator
{
   typedef Signature::Symbol SS;
   typedef LambdaElimination LE;
   typedef HOSortHelper HSH;

   PSNarrowingResultIterator(Clause* cl, Literal* l): 
    _cl(cl), _lit(l), _returned(0)
   { 

     TermList* lhs = l->args();
     TermList* rhs = lhs->next();
     
     if(value(*lhs) == -1){
      _narrowableTerm = *lhs;
     } else {
      _narrowableTerm = *rhs;
     }
  
     unsigned argnum = HSH::argNum(_narrowableTerm);
     if(argnum != 1){ 
       _toBeReturned = 0;
     } else {
       unsigned sort = HSH::getNthArgSort(_narrowableTerm, 0);
       unsigned output = HSH::outputSort(sort);
       if(output != Sorts::SRT_BOOL){
         _toBeReturned = 0;
       } else {
         _narrowedVar = HSH::getHead(_narrowableTerm).var();
         _narrowedVarSort = HSH::getHeadSort(_narrowableTerm);
         _toBeReturned = 2;
       }
     }
   }

   DECL_ELEMENT_TYPE(Clause*);
   
   bool hasNext(){
     CALL("ExtendedNarrowing::PSNarrowingResultIterator::hasNext");
     return _returned < _toBeReturned;
   }

   OWN_ELEMENT_TYPE next(){
     CALL("ExtendedNarrowing::PSNarrowingResultIterator::next");
   
     static Substitution subst;
     subst.reset();
    
     TermList quantiifer;
     
     bool added;                
     if(!_returned){
       quantiifer = LE::addHolConstant("vPI", _narrowedVarSort, added, SS::PI);
     } else {
       quantiifer = LE::addHolConstant("vSIGMA", _narrowedVarSort, added, SS::SIGMA);
     }

     subst.bind(_narrowedVar, quantiifer);

     unsigned cLen = _cl->length();
     
     Inference* inf = new Inference1(Inference::EXTENDED_NARROWING, _cl); 
     Clause* res = new(cLen) Clause(cLen, _cl->inputType(), inf);

     
     for(unsigned i=0;i<cLen;i++) {
       Literal* curr=(*_cl)[i];
       Literal* currAfter = curr->apply(subst);
       (*res)[i] = currAfter;
     }

     res->setAge(_cl->age()+1);
     env.statistics->extendedNarrows++;

     _returned++;

     //cout << "Returning " + res->toString() << endl;

     return res;  
   }

private:
   unsigned _narrowedVar;
   unsigned _narrowedVarSort;
   unsigned _toBeReturned;
   TermList _narrowableTerm;
   Clause* _cl;
   Literal* _lit;
   unsigned _returned;
};

struct ExtendedNarrowing::ResultFn
{
  ResultFn(Clause* cl): _cl(cl){}
  
  DECL_RETURN_TYPE(VirtualIterator<Clause*>);
  OWN_RETURN_TYPE operator() (pair<pair<Literal*, unsigned>, TermQueryResult> arg){

    TermQueryResult qr = arg.second;
  
    return pvi(NarrowingResultIterator(_cl, arg.first.first, arg.first.second, 
                                       qr.term, qr.substitution));
  }
  
private:
  Clause* _cl;
};

struct ExtendedNarrowing::PiSigmaResultFn
{
  PiSigmaResultFn(Clause* cl): _cl(cl){}

  DECL_RETURN_TYPE(VirtualIterator<Clause*>);
  OWN_RETURN_TYPE operator() (Literal* l){
  
    return pvi(PSNarrowingResultIterator(_cl, l));
  }

private:
  Clause* _cl;
};

struct ExtendedNarrowing::ApplicableRewritesFn
{
  typedef pair<Literal*, unsigned> pair_lit_side;
  
  ApplicableRewritesFn(ExtendedNarrowingIndex* index) : _index(index){}
  DECL_RETURN_TYPE(VirtualIterator<pair<pair_lit_side, TermQueryResult> >);
  OWN_RETURN_TYPE operator()(Literal* l)
  {
    CALL("ExtendedNarrowing::ApplicableRewritesFn()");
    
    pair_lit_side p;
    
    TermList* lhs = l->nthArgument(0);
    TermList* rhs = l->nthArgument(1);

    if(HOSortHelper::getHead(*lhs).isVar()){
      p = make_pair(l, 0);       
    } else {
      p = make_pair(l, 1);
    }
     
    return pvi( pushPairIntoRightIterator(p, _index->getUnifications((p.second ? *rhs : *lhs), true)));
  
  }
private:
  ExtendedNarrowingIndex* _index;
};

ClauseIterator ExtendedNarrowing::generateClauses(Clause* premise)
{
  CALL("ExtendedNarrowing::generateClauses");

  //cout << "ExtendedNarrowing with " << premise->toString() << endl;

  auto it1 = premise->getSelectedLiteralIterator();
  //filter out literals that are not suitable for narrowing
  auto it2 = getFilteredIterator(it1, IsNarrowableBoolEquality());

  //pair of literals and possible rewrites that can be applied to literals
  auto it3 = getMapAndFlattenIterator(it2, ApplicableRewritesFn(_index));
  
  //apply rewrite rules to literals
  auto it4 = getMapAndFlattenIterator(it3, ResultFn(premise));
  
  auto it5 = getMapAndFlattenIterator(it2, PiSigmaResultFn(premise));

  auto it6 = getConcatenatedIterator(it4, it5);

  return pvi( it6 );
  
}

}