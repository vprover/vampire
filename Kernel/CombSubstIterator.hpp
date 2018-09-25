
/*
 * File CombSubstIterator.hpp.
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
 * @file CombSubstIterator.hpp
 * Defines class CombSubstIterator.
 *
 */

#ifndef __CombSubstIterator__
#define __CombSubstIterator__

#include <utility>

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Set.hpp"
#include "Lib/Backtrackable.hpp"
#include "Lib/Deque.hpp"

#include "Indexing/Index.hpp"

#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "HOSortHelper.hpp"

#if VDEBUG

#include <iostream>
#include "Lib/VString.hpp"

#endif

namespace Kernel
{

using namespace Indexing;
using namespace Lib;

//should split into separate file
class CombSubstitution 
:public Backtrackable
{
  CLASS_NAME(CombSubstitution);
  USE_ALLOCATOR(CombSubstitution);

  public:

    CombSubstitution(TermList t1,int index1, TermList t2, int index2):
    _solved(false)
    {
      unsigned maxt1 = HOSortHelper::getMaxVar(t1);
      unsigned maxt2 = HOSortHelper::getMaxVar(t2);
      _nextFreshVar = max(maxt1, maxt2) + 1;
      _maxOrigVar = _nextFreshVar - 1;
      HOSortHelper::HOTerm ht1 = HOSortHelper::deappify(t1, index1);
      HOSortHelper::HOTerm ht2 = HOSortHelper::deappify(t2, index2);
      UnificationPair up = UnificationPair(ht1, ht2);
      _unificationPairs.push(up);
    }
    
    typedef RobSubstitution::VarSpec VarSpec;
    
    TermList apply(TermList t, int index) const;
    Literal* apply(Literal* lit, int index) const;
    HOSortHelper::HOTerm deref(VarSpec vs, bool& success) const;
    
    enum AlgorithmStep{
       UNDEFINED,
       ADD_ARG,
       SPLIT,
       I_NARROW,
       K_NARROW,
       KX_NARROW,
       B_NARROW,
       BX_NARROW,
       C_NARROW,
       CX_NARROW,
       S_NARROW,
       SX_NARROW,
       I_REDUCE,
       K_REDUCE,
       B_REDUCE,
       C_REDUCE,
       S_REDUCE,
       DECOMP,
       ELIMINATE,
       ID //syntactically identical
    };
    
    /**
      * Used to record whether the algorithm step can be applied to 
      * the left of the pair, the right or applies to both (for example
      * ADD_ARG and DECOMP apply to both items in a unif pair).
      */
    enum ApplyTo{
       FIRST = 1,
       SECOND = 2,
       BOTH = 3
    };

  #if VDEBUG
    //need to add boolean option to allow "collapsing of substitution"
    vstring toString();
  #endif
          
  private:

    typedef pair<AlgorithmStep, ApplyTo>  Transform;
    typedef Stack<Transform> TransformStack;
    typedef Signature::Symbol SS;
    typedef HOSortHelper HSH;
    typedef pair<HSH::HOTerm,HSH::HOTerm> UnifPair;  

    struct UnificationPair
    {
      //CLASS_NAME(UnificationPair);
      //USE_ALLOCATOR(UnificationPair);
      UnificationPair(HSH::HOTerm ht1, HSH::HOTerm ht2)
      {
        unifPair = make_pair(ht1,ht2);
        lsLeft = UNDEFINED;
        slsLeft = UNDEFINED;
        lsRight = UNDEFINED;
        slsRight = UNDEFINED;
      }
      //WARNING code uses default shellow copy constructor!
      UnificationPair(HSH::HOTerm tl, HSH::HOTerm tr, 
                      AlgorithmStep lsl, AlgorithmStep slsl, AlgorithmStep lsr, AlgorithmStep slsr)
      : lsLeft(lsl), slsLeft(slsl), lsRight(lsr), slsRight(slsr)
      {
        unifPair = make_pair(tl,tr);
      }
      //stack that holds the potential transformations that can be carried out to
      //the left-hand (first) term of this unification pair
      TransformStack transformsLeft;
      TransformStack transformsRight;
      TransformStack transformsBoth;
      
    #if VDEBUG
      vstring toString() const{
        vstring res = "<" + unifPair.first.toString() + " , " +
                            unifPair.second.toString() + ">";
        return res;
      }
    #endif    
      AlgorithmStep lsLeft;      
      AlgorithmStep slsLeft;
      AlgorithmStep lsRight;      
      AlgorithmStep slsRight;
      UnifPair unifPair;
    };

   #if VDEBUG
    vstring unificationPairsToString(){
      vstring res;
      res =  "PRINTING THE UNIFICATION PAIRS \n";
      for(int i = _unificationPairs.size() -1; i >=0; i--){
         res += "<" + _unificationPairs[i].unifPair.first.toString(false, true) + " , " + 
                      _unificationPairs[i].unifPair.second.toString(false, true)  + ">\n";
      }
      return res;
    }
    
    vstring algorithmStepToString(AlgorithmStep as){
      switch(as){
       case SPLIT:
         return "SPLIT";
       case I_NARROW:
         return "I_NARROW";
       case K_NARROW:
         return "K_NARROW";
       case KX_NARROW:
         return "KX_NARROW";
       case B_NARROW:
         return "B_NARROW";
       case BX_NARROW:
         return "BX_NARROW";
       case C_NARROW:
         return "C_NARROW";
       case CX_NARROW:
         return "CX_NARROW";
       case S_NARROW:
         return "S_NARROW";
       case SX_NARROW:
         return "SX_NARROW";
       case I_REDUCE:
         return "I_REDUCE";
       case K_REDUCE:
         return "K_REDUCE";
       case B_REDUCE:
         return "B_REDUCE";
       case C_REDUCE:
         return "C_REDUCE";
       case S_REDUCE:
         return "S_REDUCE";
       case DECOMP:
         return "DECOMP";
       case ELIMINATE:  
         return "ELIMINATE"; 
       case ID:
         return "ID"; 
       case ADD_ARG:
         return "ADD_ARG";   
       default:
         return "UNKNOWN";
      }
    }
   #endif   
    
    TransformStack availableTransforms();
    /*
     * Finds all relevant trandformations for top unif pair 
     * in _unifcationPairs of _unifSystem. Populates transformation
     * stacks.
     */
    void populateTransformations(UnificationPair&);   
    void populateSide(HSH::HOTerm&, ApplyTo, TransformStack&,AlgorithmStep,AlgorithmStep);
    /** returns the particular narrow step relevant to the arg */
    AlgorithmStep reduceStep(HSH::HOTerm&) const;
    /** Carry out transformation represented bt t on top pair*/ 
    bool transform(Transform t);

    void transform(HSH::HOTerm&, HSH::HOTerm&, AlgorithmStep);
    void iReduce(HSH::HOTerm&)const;
    void kReduce(HSH::HOTerm&)const;
    void bcsReduce(HSH::HOTerm&, AlgorithmStep)const;

    bool canPerformStep(AlgorithmStep, AlgorithmStep, AlgorithmStep);
    bool occurs(const VarSpec, const HSH::HOTerm&);
    void eliminate(VarSpec, HSH::HOTerm);
    void eliminate(VarSpec, HSH::HOTerm, HSH::HOTerm&);
    void addToSolved(VarSpec, HSH::HOTerm);
    void pushNewPair(HSH::HOTerm&, HSH::HOTerm&, AlgorithmStep, AlgorithmStep, AlgorithmStep, AlgorithmStep);
                     
    inline HSH::HOTerm newVar(unsigned sort, int index){
      CALL("CombSubstitution::newvar");
      HSH::HOTerm ht = HSH::HOTerm(TermList(_nextFreshVar, false), sort, index);
      _nextFreshVar++;
      return ht;
    }
    inline bool introduced(unsigned var){
      return var > _maxOrigVar;
    }

    //if subsitution represents solved system _solved set to true
    bool _solved;
    unsigned _nextFreshVar;
    unsigned _maxOrigVar;

    Stack<UnificationPair> _unificationPairs;
    
    typedef DHMap<VarSpec,HSH::HOTerm,VarSpec::Hash1, VarSpec::Hash2> SolvedType;
    mutable SolvedType _solvedPairs;
  
    class BindingBacktrackObject
    : public BacktrackObject
    {
    public:
      BindingBacktrackObject(CombSubstitution* subst, VarSpec v)
      :_subst(subst), _var(v)
      {}

      void backtrack()
      {
        _subst->_solvedPairs.remove(_var);
      }

      CLASS_NAME(CombSubstitution::BindingBacktrackObject);
      USE_ALLOCATOR(BindingBacktrackObject);
    private:
      CombSubstitution* _subst;
      VarSpec _var;
    };

    class StackBacktrackObject
    : public BacktrackObject
    {
    public:
      StackBacktrackObject(CombSubstitution* subst, Stack<UnificationPair> st)
      :_subst(subst), _st(st), _freshVarNum(_subst->_nextFreshVar)
      {}
      
      void backtrack()
      {
        // Not particularly elegant or efficient. 
        // Just resetting the whole stack
        // Should only be resetting elements that have changed.
        _subst->_unificationPairs = _st;
        _subst->_nextFreshVar = _freshVarNum;
      }
  
    #if VDEBUG
      vstring toString() const {
        vstring res;
        for (int i = _st.size() -1; i >= 0; i--){
          res+= _st[i].toString() + "\n";
        }
        return res;
      }
    #endif

      CLASS_NAME(CombSubstitution::StackBacktrackObject);
      USE_ALLOCATOR(StackBacktrackObject);
    private:
      CombSubstitution* _subst;
      Stack<UnificationPair> _st;
      unsigned _freshVarNum;
    };

    friend class CombSubstIterator;
};

class CombSubstIterator
: public IteratorCore<CombSubstitution*>
{
public:
  CLASS_NAME(CombSubstIterator);
  USE_ALLOCATOR(CombSubstIterator);
  
  CombSubstIterator(TermList t1,int index1, TermList t2, int index2)
  {
    _unifSystem = new CombSubstitution(t1, index1, t2, index2);
    cout << "STARTING ITERATOR WITH " + _unifSystem->_unificationPairs.top().toString() << endl;
    transformStacks.push(_unifSystem->availableTransforms());
    _calledNext = false;
  }

  bool hasNext(){
    if(!_calledNext){
      if(_unifSystem->_solved){
        return true;
      }
    }
    _calledNext = false;
    return hasNextUnifier();
  }
  /* 
   * Only valid if has been previous call to hasNext that
   * has returned true! Calling next multiple times for one
   * call of hasNext will result in the same unifier being return
   * multiple times.
   */
  CombSubstitution* next(){
    _calledNext = true;
    return _unifSystem;
  }

#if VDEBUG
  vstring bdStackToString() {
    vstring res;
    unsigned count = 0;
    for(int i = bdStack.size() - 1; i >= 0; i--){
      count++;
      res += bdStack[i].toString();
      if(count > 2){
        break;
      }
    }
    return res;
  }
#endif

private:

  typedef CombSubstitution::AlgorithmStep AlgorithmStep;
  typedef CombSubstitution::ApplyTo ApplyTo;
  typedef pair<AlgorithmStep,ApplyTo> Transform;
  typedef Stack<Transform> TransformStack;

  /** Copy constructor is private and without a body, because we don't want any. */
  CombSubstIterator(const CombSubstIterator& obj);
  /** operator= is private and without a body, because we don't want any. */
  CombSubstIterator& operator=(const CombSubstIterator& obj);


  CombSubstitution* _unifSystem;
  Stack<TransformStack> transformStacks;
  Stack<BacktrackData> bdStack;
  bool _calledNext;

  bool hasNextUnifier();
  /** apply transformation t to the top unification pair in current system
   *  record any chanegs in bd so that transformation can be reversed
   */
  bool transform(Transform t, BacktrackData& bd);

};

}
#endif /*__CombSubstIterator____*/