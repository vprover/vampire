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
 * @file Backtrackable.hpp
 * Defines class Backtrackable
 */

#ifndef __Backtrackable__
#define __Backtrackable__

#include "List.hpp"
#include "Int.hpp"
#include "Lib/Stack.hpp"

namespace Lib
{

class BacktrackData;

/**
 * Object that represents a single change to the @b Backtrackable object
 *
 * @b BacktrackObject objects are stored in object @b BacktrackData and
 * a client of a @b Backtrackable object should not directly encounter them.
 */
class BacktrackObject
{
public:
#if VDEBUG
  /**
   * Create a new backtrack object
   */
  BacktrackObject() : _next(0) {}
#endif
  virtual ~BacktrackObject()  {}

  /**
   * Undo the action represented by this backtrack object
   */
  virtual void backtrack() = 0;

#if VDEBUG
  virtual std::string toString() const { return "(backtrack object)"; }
#endif
  template<class F> 
  static BacktrackObject* fromClosure(F f);
private:
  /**
   * Pointer to the @b BacktrackObject that is previous (i.e. next older) in the
   * @b BacktrackData structure that contains this object
   */
  BacktrackObject* _next;

  friend class BacktrackData;
  template<class F> friend class BacktrackClosure;
};

template<class F>
class BacktrackClosure : public BacktrackObject
{
  F _fun;
public:
  USE_ALLOCATOR(BacktrackClosure);
  BacktrackClosure(BacktrackClosure&&) = default;
  BacktrackClosure& operator=(BacktrackClosure&&) = default;
  
  BacktrackClosure(F fun) : _fun(std::move(fun)) {}
  void backtrack() { _fun(); }
};

template<class F> 
BacktrackObject* BacktrackObject::fromClosure(F f) { return new BacktrackClosure<F>(std::move(f)); }


/**
 * Class of objects used to store the change history of
 * @b Backtrackable objects
 *
 * The @b BacktrackData object contains a list of records of what
 * can be backtracked. In order to avoid a memory leak, either the
 * @b backtrack or the @b drop function must always be called.
 *
 * The @b BacktrackData object has a shallow copy constructor, so
 * always at most one copy of the @b BacktrackData object should be
 * considered valid. Otherwise the behavior is undefined, as it may
 * lead to errors such as repeated deletion of list elements.
 */
class BacktrackData
{
public:
  BacktrackData() : _boList(0) {}

  /**
   * Backtrack changes stored in this object
   *
   * After a call to this function, the object is empty as new.
   */
  void backtrack()
  {
    BacktrackObject* curr=_boList;
    BacktrackObject* next;
    while(curr) {
      curr->backtrack();
      next=curr->_next;
      delete curr;
      curr=next;
    }
    _boList=0;
  }

  /**
   * Remove changes stored in this object
   *
   * After a call to this function, the object is empty as new.
   */
  void drop()
  {
    BacktrackObject* curr=_boList;
    BacktrackObject* next;
    while(curr) {
      next=curr->_next;
      delete curr;
      curr=next;
    }
    _boList=0;
  }

  /**
   * Add a backtrack object @b bo to his object, so that the action
   * represented by it can be backtracked by a call to the @b backtrack
   * function
   */
  void addBacktrackObject(BacktrackObject* bo)
  {
    ASS_EQ(bo->_next,0);
    bo->_next=_boList;
    _boList=bo;
  }

  template<class F>
  void addClosure(F function)
  { addBacktrackObject(BacktrackObject::fromClosure(std::move(function))); }

  /**
   * Move all BacktrackObjects from @b this to @b bd. After the
   * operation, @b this is empty.
   */
  void commitTo(BacktrackData& bd)
  {
    if(!_boList) {
      return;
    }
    BacktrackObject* lastOwn=_boList;
    while(lastOwn->_next) {
      lastOwn=lastOwn->_next;
    }
    lastOwn->_next=bd._boList;
    bd._boList=_boList;
    _boList=0;
  }

  /**
   * Return true iff the object does not contain records of any
   * backtrackable actions
   */
  bool isEmpty() const
  {
    return _boList==0;
  }

  /**
   * Set value of @b *ptr to @b val and store appropriate recrd into
   * this object, so that the action can later be backtracked
   */
  template<typename T>
  void backtrackableSet(T* ptr, T val)
  {
    addBacktrackObject(new SetValueBacktrackObject<T>(ptr,*ptr));
    *ptr=val;
  }

#if VDEBUG
  std::string toString()
  {
    std::string res;
    unsigned cnt=0;
    BacktrackObject* bobj=_boList;
    while(bobj) {
      res+=bobj->toString()+"\n";
      cnt++;
      bobj=bobj->_next;
    }
    res+="object cnt: "+Int::toString(cnt)+"\n";
    return res;
  }
#endif

  /**
   * List-like structure of @b BacktrackObject objects representing
   * backtrackable changes stored in this object
   *
   * The backtrackable strucure is built by pointers in
   * @b BacktrackObject::_next
   */
  BacktrackObject* _boList;
private:

  /**
   * An auxiliary class to support the @b backtrackableSet function
   */
  template<typename T>
  class SetValueBacktrackObject
  : public BacktrackObject
  {
  public:
    SetValueBacktrackObject(T* addr, T previousVal)
    : addr(addr), previousVal(previousVal) {}
    void backtrack()
    {
      *addr=previousVal;
    }
  private:
    T* addr;
    T previousVal;
  };
};


/**
 * A parent class for objects that allow for being restored
 * to their previous state
 *
 * When a client wants to be able to later restore the object
 * to its current state, he calls the @b bdRecord function which
 * starts recording changes made to the object to the backtrack
 * data storage represented by the @b bd object of type
 * @b BacktrackData.
 *
 * After the change that should be backtrackable are
 * done, client calls the @b bdDone function to stop recording.
 *
 * Changes of multiple objects can be stored into one @b bd object.
 *
 * To backtrack the changes client can call the @b BacktrackData::backtrack
 * function. All involved objects must be in the same state as
 * when the @b bdDone function was called.
 *
 * Recording requests are stored as a stack in the object, so
 * when client wants to record into other @b bd object, he should
 * call again the @b bdRecord function, and when he calls the
 * @b bdDone function, recording to the previous object is restored.
 *
 * If, in a similar manner, object changes should be ignored for a period
 * of time, the @b bdDoNotRecord function can be called instead
 * of te @b bdRecord one. (The previous state is again restored
 * by a call to the @b bdDone function.)
 */
class Backtrackable
{
public:
#if VDEBUG
  /**
   * Destroy the Backtrackable object
   *
   * Ensures that calls to @b bdRecord / @b bdDoNotRecord and
   * @b bdDone were properly paired.
   */
  ~Backtrackable() { ASS_EQ(_bdStack.size(),0); }
#endif
  /**
   * Start recording object changes into the @b bd object
   *
   * The recording is stopped by a call to the @b bdDone function.
   */
  void bdRecord(BacktrackData& bd)
  { _bdStack.push(&bd); }

  /**
   * Start ignoring object changes instead of possibly recording them
   * for some client
   *
   * The ignoring is stopped by a call to the @b bdDone function.
   */
  void bdDoNotRecord()
  { _bdStack.push(nullptr); }

  /**
   * Finish a request on recording or ignoring object changes and get
   * to a previous one if it exists
   *
   * @see Backtrackable
   */
  void bdDone()
  { _bdStack.pop(); }

  /**
   * Move all change records from @b bd to the BacktrackData object associated
   * with this object. If there is no such object, the backtrack data from the
   * @c bd object are simply dropped.
   * The @b bd object
   * is empty after call to his function.
   */
  void bdCommit(BacktrackData& bd)
  {
    ASS(!bdIsRecording() || &bd!=&bdGet());

    if(bdIsRecording()) {
      bd.commitTo(bdGet());
    }
    else {
      bd.drop();
    }
  }

protected:
  /**
   * Initialize a Backtrackable object
   */
  Backtrackable() : _bdStack() {}

  /**
   * Return true iff we are currently recording object changes
   */
  bool bdIsRecording()
  {
    return !_bdStack.isEmpty() && _bdStack.top() != nullptr;
  }

  /**
   * Add a BacktrackObject to the @b BacktrackData object that
   * records changes to this object
   *
   * The BacktrackObject represents a single backtrackable change
   * performed on this object.
   */
  void bdAdd(BacktrackObject* bo)
  {
    ASS(bdIsRecording());

    bdGet().addBacktrackObject(bo);
  }

  /**
   * Return reference to the @b BacktrackData object to which
   * we are currently recording
   */
  BacktrackData& bdGet()
  {
    ASS(bdIsRecording());

    return *_bdStack.top();
  }
private:
  /**
   * A list that is being used as a stack that stores current
   * @b bdRecord requests
   *
   * A list link that contains 0 at the place of the @b BacktrackData
   * pointer corresponds to a @b bdDoNotRecord call.
   */
  Stack<BacktrackData*> _bdStack;
};

};

#endif // __Backtrackable__
