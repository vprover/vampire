
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
#include "Lib/SmartPtr.hpp"

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
  
    typedef HOSortHelper HSH;
    typedef RobSubstitution::VarSpec VarSpec;
    typedef SmartPtr<HSH::HOTerm> HOTerm_ptr;
  
    CombSubstitution(TermList t1, int index1, TermList t2, int index2,
                     unsigned sort):
    _solved(false),_nextFreshVar(0), _nextUnboundAvailable(0)
    {
      //if t1 or t2 are vars, need to provide sorts...
      HOTerm_ptr ht1 = HOSortHelper::deappify(t1, index1, sort);
      HOTerm_ptr ht2 = HOSortHelper::deappify(t2, index2, sort);
      UnificationPair up = UnificationPair(ht1, ht2);
      _unificationPairs.push(up);
    }

    ~CombSubstitution(){}
    
    static const int UNBOUND_INDEX = -2;
    static const int AUX_INDEX = -3;

    TermList apply(TermList t, int index, int sort = -1) const;
    Literal* apply(Literal* lit, int index) const;
    HOTerm_ptr deref(VarSpec vs, bool& success, unsigned sort) const;
    
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

    enum PairType{
      FLEX_FLEX_SAME_HEAD = 0,
      FLEX_FLEX_DIFF_HEAD = 1,
      FLEX_RIGID_LEFT = 2,
      FLEX_RIGID_RIGHT = 3,
      RIGID_RIGID = 4
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

    struct UnificationPair
    {
      //CLASS_NAME(UnificationPair);
      //USE_ALLOCATOR(UnificationPair);
      
      UnificationPair(HOTerm_ptr ht1, HOTerm_ptr ht2)
      {
        terml = ht1;
        termr = ht2;        
        lsLeft = UNDEFINED;
        slsLeft = UNDEFINED;
        lsRight = UNDEFINED;
        slsRight = UNDEFINED;
        mostRecentSide = BOTH;
      }
      
      UnificationPair(HOTerm_ptr tl, HOTerm_ptr tr, 
      AlgorithmStep lsl, AlgorithmStep slsl, AlgorithmStep lsr, AlgorithmStep slsr, ApplyTo mr)
      : lsLeft(lsl), slsLeft(slsl), lsRight(lsr), slsRight(slsr), mostRecentSide(mr)
      {
        terml = tl;
        termr = tr;
      }
      //stack that holds the potential transformations that can be carried out to
      //the left-hand (first) term of this unification pair
      TransformStack transformsLeft;
      TransformStack transformsRight;
      TransformStack transformsBoth;
     
      void emptyTransforms(){
        while(!transformsLeft.isEmpty()){
          transformsLeft.pop();
        }
        while(!transformsRight.isEmpty()){
          transformsRight.pop();
        }
        while(!transformsBoth.isEmpty()){
          transformsBoth.pop();
        }        
      }

      PairType getPairType() {      
        if(terml->varHead()){
          if(termr->varHead()){
            if(terml->sameVarHead(termr, true)){
              return FLEX_FLEX_SAME_HEAD;
            } else {
              return FLEX_FLEX_DIFF_HEAD;
            }
          } else {
            return FLEX_RIGID_LEFT;
          }
        } else if(termr->varHead()){
          return FLEX_RIGID_RIGHT;
        }
        return RIGID_RIGID;
      }
     
    #if VDEBUG
      vstring toString() const{
        vstring res = "<" + terml->toString() + " of sort " + 
                            env.sorts->sortName(terml->srt) + " , \n\n" +
                            termr->toString() + " of sort " + 
                            env.sorts->sortName(termr->srt) + ">";
        return res;
      }
    #endif
      AlgorithmStep lsLeft;      
      AlgorithmStep slsLeft;
      AlgorithmStep lsRight;
      AlgorithmStep slsRight;
      ApplyTo mostRecentSide;
      //get rid of this pair and make two HOTerms
      HOTerm_ptr terml;
      HOTerm_ptr termr;
    };

   #if VDEBUG
    vstring unificationPairsToString(){
      vstring res;
      res =  "PRINTING THE UNIFICATION PAIRS \n";
      for(int i = _unificationPairs.size() -1; i >=0; i--){
         res += "<" + _unificationPairs[i].terml->toString(false, true) + " , " + 
                      _unificationPairs[i].termr->toString(false, true)  + ">\n";
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
         return "UNDEFINED";
      }
    }
   #endif   
    
    TransformStack availableTransforms();
    /*
     * Finds all relevant transformations for top unif pair 
     * in _unifcationPairs of _unifSystem. Populates transformation
     * stacks.
     */
    void populateTransformations(UnificationPair&);   
    void populateSide(HOTerm_ptr, ApplyTo, TransformStack&,AlgorithmStep,AlgorithmStep);
    /** returns the particular narrow step relevant to the arg */
    AlgorithmStep reduceStep(const HOTerm_ptr) const;
    /** Carry out transformation represented bt t on top pair
        If further options set to true, unification system prior 
        to carrying out transform will be saved to backtrack to.
        Otherwise not */    
    bool transform(Transform t, bool furtherOptions);

    void transform(HOTerm_ptr, HOTerm_ptr, AlgorithmStep);
    void iReduce(HOTerm_ptr)const;
    void kReduce(HOTerm_ptr)const;
    void bcsReduce(HOTerm_ptr, AlgorithmStep)const;

    bool canPerformStep(AlgorithmStep, AlgorithmStep, AlgorithmStep);
    bool occursOrNotPure(const VarSpec&, HOTerm_ptr);
    void eliminate(const VarSpec&, HOTerm_ptr);
    void eliminate(const VarSpec&, HOTerm_ptr, HOTerm_ptr);
    void addToSolved(const VarSpec&, HOTerm_ptr);
    void pushNewPair(HOTerm_ptr ht1, HOTerm_ptr ht2){
      UnificationPair newup = UnificationPair(ht1, ht2);
      _unificationPairs.push(newup); 
    }
    bool isDummyArg(HOTerm_ptr ht) const {
      CALL("CombSubstitution::isDummyArg");
      
      if(!ht->varHead()){
        SS* sym = env.signature->getFunction(ht->head.term()->functor());
        return sym->isDummyArg();        
      }
      return false;
    }
                     
    inline HOTerm_ptr newVar(unsigned sort, int index){
      CALL("CombSubstitution::newvar");
      HOTerm_ptr ht = HOTerm_ptr(new HSH::HOTerm(TermList(_nextFreshVar++, false), sort, AUX_INDEX));
      return ht;
    }
    //inline bool introduced(unsigned var){
    //  return var > _maxOrigVar;
    //}

    //if subsitution represents solved system _solved set to true
    bool _solved;
    unsigned _nextFreshVar;
    mutable unsigned _nextUnboundAvailable;
    Stack<UnificationPair> _unificationPairs;
    
    typedef DHMap<VarSpec,HOTerm_ptr,VarSpec::Hash1, VarSpec::Hash2> SolvedType;
    mutable SolvedType _solvedPairs;
    mutable SolvedType _unboundVariables;
  
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
      :_subst(subst), _freshVarNum(_subst->_nextFreshVar)
      {
        for(unsigned i = 0; i < st.size(); i++){
         HOTerm_ptr htpl = HOTerm_ptr(new HSH::HOTerm(*(st[i].terml)));
         HOTerm_ptr htpr = HOTerm_ptr(new HSH::HOTerm(*(st[i].termr)));
         UnificationPair up = 
            UnificationPair(htpl, htpr, st[i].lsLeft, st[i].slsLeft, st[i].lsRight, st[i].slsRight, st[i].mostRecentSide);
          _st.push(up);
        }
      }
      
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
  
  CombSubstIterator(TermList t1, unsigned s1, int index1,
                   TermList t2, unsigned s2, int index2)
  {
    ASS(s1 == s2);
    _unifSystem = new CombSubstitution(t1, index1, t2, index2, s1);
    transformStacks.push(_unifSystem->availableTransforms());
    cout << "STARTING ITERATOR WITH " + _unifSystem->_unificationPairs.top().toString() << endl; 
    //cout << transformStacksToString() << endl;
    _calledNext = false;
  }

  ~CombSubstIterator(){
    delete _unifSystem;
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
    ASS(_unifSystem->_solved);
    _calledNext = true;
    _unifSystem->_nextUnboundAvailable = 0;
    _unifSystem->_unboundVariables.reset();
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

  vstring transformStacksToString() {
    vstring res = "TRANSFORM STACK: \n";
    for(int i = transformStacks.size() - 1; i >= 0; i--){
      res += "[";
      for(int j = transformStacks[i].size()-1; j >=0; j--){
        vstring side;
        if(transformStacks[i][j].second == CombSubstitution::FIRST){
          side = ", LEFT), ";
        }else if(transformStacks[i][j].second == CombSubstitution::SECOND){
          side = ", RIGHT), ";
        }else{
          side = ", ";
        }
        res += "(" + _unifSystem->algorithmStepToString(transformStacks[i][j].first) + side;
      }
      res += "]\n";
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
  bool transform(Transform t, bool b, BacktrackData& bd);

};

}
#endif /*__CombSubstIterator____*/